#!/usr/bin/env python3
"""Fail-closed, signature-driven Eunoia signature to Rocq data compiler.

This compiles syntax and computations, never SMT semantics or proof evidence.
Only explicitly selected rules and their transitive dependencies are emitted.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import sys


class SignatureError(ValueError):
    pass


@dataclass(frozen=True)
class Node:
    value: str | tuple[Node, ...]
    kind: str
    path: Path
    line: int

    def error(self, message):
        raise SignatureError(f"{self.path}:{self.line}: {message}")


def atom(n: Node) -> str:
    if n.kind != "symbol":
        n.error("expected an unquoted symbol")
    return n.value


def seq(n: Node) -> tuple[Node, ...]:
    if n.kind != "list":
        n.error("expected a list")
    return n.value


def parse(text: str, path: Path) -> list[Node]:
    """SMT-LIB strings, quoted symbols and comments are lexed separately."""
    tokens = []
    i, line = 0, 1
    while i < len(text):
        c = text[i]
        if c.isspace():
            line += c == "\n"
            i += 1
        elif c == ";":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif c in "()":
            tokens.append(Node(c, c, path, line))
            i += 1
        elif c in '\"|':
            start, start_line, quote = i, line, c
            i += 1
            content = ""
            while i < len(text):
                c = text[i]
                if c == quote:
                    if quote == '"' and i + 1 < len(text) and text[i + 1] == '"':
                        content += '"'
                        i += 2
                        continue
                    i += 1
                    break
                if c == "\\":
                    raise SignatureError(f"{path}:{line}: backslash escapes unsupported")
                line += c == "\n"
                content += c
                i += 1
            else:
                raise SignatureError(f"{path}:{start_line}: unterminated literal at {start}")
            tokens.append(Node(content, "string" if quote == '"' else "quoted", path, start_line))
        else:
            start = i
            while i < len(text) and not text[i].isspace() and text[i] not in '();"|':
                i += 1
            tokens.append(Node(text[start:i], "symbol", path, line))
    stack, result = [], []
    for t in tokens:
        if t.kind == "(":
            stack.append((t, []))
        elif t.kind == ")":
            if not stack:
                t.error("unexpected closing parenthesis")
            start, children = stack.pop()
            n = Node(tuple(children), "list", path, start.line)
            (stack[-1][1] if stack else result).append(n)
        else:
            (stack[-1][1] if stack else result).append(t)
    if stack:
        stack[-1][0].error("unclosed parenthesis")
    return result


def raw(n: Node):
    return [raw(c) for c in seq(n)] if n.kind == "list" else (n.kind, n.value)


def quoted(s):
    if not s.isascii() or any(ord(c) < 32 for c in s):
        raise SignatureError("non-ASCII/control characters unsupported in generated symbols")
    return '"' + s.replace('"', '""') + '"'


def lst(items):
    return "[" + "; ".join(items) + "]"


def apply_ir(head, args, constructor):
    for arg in args:
        head = f"({constructor} {head} {arg})"
    return head


class Compiler:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.files = {}
        self.decls = {}
        self.overloaded = set()
        self.programs = {}
        self.rules = {}
        self.used_symbols = set()
        self.list_vars = set()
        self.natives = set()
        self.definitions = set()
        self.gensym = 0
        self.read(self.root, [])

    def read(self, path, active):
        path = path.resolve()
        if path in active:
            raise SignatureError(f"{path}: include cycle")
        if path in self.files:
            return
        try:
            data = path.read_bytes()
            forms = parse(data.decode("utf-8"), path)
        except (OSError, UnicodeError) as ex:
            raise SignatureError(f"{path}: {ex}") from ex
        self.files[path] = hashlib.sha256(data).hexdigest()
        for form in forms:
            fields = seq(form)
            if not fields:
                form.error("empty top-level form")
            cmd = atom(fields[0])
            if cmd == "include":
                if len(fields) != 2 or fields[1].kind != "string":
                    form.error("include must have one string path")
                self.read(path.parent / fields[1].value, active + [path])
                continue
            if cmd not in {"declare-rule", "declare-const", "declare-consts",
                           "declare-parameterized-const", "program", "define"}:
                form.error(f"unsupported top-level command {cmd}")
            if len(fields) < 3:
                form.error("incomplete declaration")
            name = atom(fields[1])
            if cmd == "declare-consts":
                # Literal-family declarations cannot be called as symbols.
                continue
            old = self.decls.get(name)
            if old:
                old_fields = seq(old)
                constants = {"declare-const", "declare-parameterized-const"}
                if cmd in constants and atom(old_fields[0]) in constants:
                    if raw(form) == raw(old):
                        form.error(f"duplicate declaration {name}")
                    self.overloaded.add(name)
                    continue
                # CPC has program prototypes followed by a full definition.
                if cmd == atom(old_fields[0]) == "program":
                    if [raw(x) for x in fields[3:6]] != [raw(x) for x in old_fields[3:6]]:
                        form.error(f"conflicting prototype for {name}")
                    if len(fields) == 6 and len(old_fields) == 7:
                        continue
                    if len(fields) == 7 and len(old_fields) == 6:
                        self.decls[name] = form
                        continue
                form.error(f"duplicate declaration {name}")
            self.decls[name] = form

    def binders(self, n):
        scope, types, explicit = {}, [], []
        self.list_vars = set()
        for b in seq(n):
            parts = seq(b)
            if len(parts) not in (2, 3):
                b.error("unsupported binder shape")
            name = atom(parts[0])
            if name in scope:
                b.error(f"duplicate binder {name}")
            attr = atom(parts[2]) if len(parts) == 3 else None
            if attr not in {None, ":implicit", ":list", ":opaque"}:
                b.error("unsupported binder attribute")
            ty = self.type_pattern(parts[1], scope)
            ident = len(scope)
            scope[name] = ident
            types.append(f"({ident}, {ty})")
            if attr == ":list":
                self.list_vars.add(name)
            if attr != ":implicit":
                explicit.append(parts[0])
        return scope, lst(types), explicit

    def substitute(self, n, substitutions):
        if n.kind == "symbol":
            return substitutions.get(n.value, n)
        if n.kind == "list":
            fs = seq(n)
            if fs and fs[0].kind == "symbol" and atom(fs[0]) == "eo::define":
                pairs = [seq(b) for b in seq(fs[1])]
                bindings = tuple(Node((b[0], self.substitute(b[1], substitutions)), "list", n.path, n.line) for b in pairs)
                body_subs = {k: v for k, v in substitutions.items() if k not in {atom(b[0]) for b in pairs}}
                return Node((fs[0], Node(bindings, "list", n.path, n.line), self.substitute(fs[2], body_subs)), "list", n.path, n.line)
            return Node(tuple(self.substitute(c, substitutions) for c in fs), n.kind, n.path, n.line)
        return n

    def symbols(self, n):
        if n.kind == "symbol":
            return {n.value}
        if n.kind == "list":
            return set().union(*(self.symbols(c) for c in seq(n)))
        return set()

    def expand(self, n, active=()):
        fs = seq(n) if n.kind == "list" else (n,)
        if not fs or fs[0].kind != "symbol":
            return n
        name = atom(fs[0])
        decl = self.decls.get(name)
        if not decl or atom(seq(decl)[0]) != "define":
            return n
        if name in active:
            n.error("recursive definition expansion")
        self.definitions.add(name)
        ds = seq(decl)
        params = [seq(b) for b in seq(ds[2])]
        explicit = [b for b in params if len(b) == 2 or atom(b[2]) != ":implicit"]
        args = fs[1:]
        # Zero-argument aliases can themselves be applied.
        if not explicit:
            body = self.expand(ds[3], active + (name,))
            if args:
                bs = seq(body) if body.kind == "list" else (body,)
                body = Node(tuple(bs) + tuple(args), "list", n.path, n.line)
            return body
        if len(args) != len(explicit):
            n.error(f"{name}: expected {len(explicit)} definition arguments")
        subs = {atom(b[0]): a for b, a in zip(explicit, args)}
        for b in params:
            if len(b) == 3 and atom(b[2]) == ":implicit":
                tname = atom(b[0])
                candidates = [subs[atom(v[0])] for v in explicit
                              if v[1].kind == "symbol" and atom(v[1]) == tname]
                if candidates:
                    subs[tname] = Node((Node("eo::typeof", "symbol", n.path, n.line), candidates[0]), "list", n.path, n.line)
        # Expansion is lexical: eo::define's local names are freshened before substitution.
        body = self.freshen(ds[3], set(subs), [0])
        return self.expand(self.substitute(body, subs), active + (name,))

    def freshen(self, n, avoid, counter):
        if n.kind != "list":
            return n
        fs = seq(n)
        if fs and fs[0].kind == "symbol" and atom(fs[0]) == "eo::define":
            pairs = [seq(b) for b in seq(fs[1])]
            if any(len(b) != 2 for b in pairs):
                n.error("malformed eo::define binding")
            if len({atom(b[0]) for b in pairs}) != len(pairs):
                n.error("duplicate eo::define binding")
            renames, bindings = {}, []
            forbidden = avoid | self.symbols(n) | set(self.decls)
            for pair in pairs:
                self.gensym += 1
                name = f"$eoc.local.{self.gensym}"
                while name in forbidden:
                    self.gensym += 1
                    name = f"$eoc.local.{self.gensym}"
                forbidden.add(name)
                fresh = Node(name, "symbol", n.path, n.line)
                renames[atom(pair[0])] = fresh
                bindings.append(Node((fresh, self.freshen(pair[1], forbidden, counter)), "list", n.path, n.line))
            body = self.substitute(fs[2], renames)
            return Node((fs[0], Node(tuple(bindings), "list", n.path, n.line), self.freshen(body, forbidden, counter)), "list", n.path, n.line)
        return Node(tuple(self.freshen(c, avoid, counter) for c in fs), "list", n.path, n.line)

    def type_pattern(self, n, scope):
        n = self.expand(n)
        if n.kind == "list":
            fs = seq(n)
            if atom(fs[0]) == "->" and len(fs) > 3:
                rest = Node((fs[0],) + fs[2:], "list", n.path, n.line)
                return f"(PApply (PApply (PSymbol {quoted('->')}) {self.type_pattern(fs[1], scope)}) {self.type_pattern(rest, scope)})"
            return apply_ir(self.type_pattern(fs[0], scope),
                            [self.type_pattern(a, scope) for a in fs[1:]], "PApply")
        name = atom(n)
        if name in scope:
            return f"(PVar {scope[name]})"
        if name not in {"Type", "Bool", "->", "eo::List", "eo::quote"} and name not in self.decls:
            n.error(f"unsupported atomic type {name}")
        return f"(PSymbol {quoted(name)})"

    def attributes(self, name):
        decl = self.decls.get(name)
        if not decl:
            return ()
        fs = seq(decl)
        if atom(fs[0]) == "declare-const":
            return fs[3:]
        if atom(fs[0]) == "declare-parameterized-const":
            return fs[4:]
        return ()

    def nil_node(self, name):
        if name == "eo::List::cons":
            d = self.root
            return Node("eo::List::nil", "symbol", d, 1)
        attrs = self.attributes(name)
        for i, attr in enumerate(attrs):
            if attr.kind == "symbol" and atom(attr) == ":right-assoc-nil":
                return self.expand(attrs[i + 1])
        return None

    def symbol(self, n, arity):
        name = atom(n)
        if name in {"true", "false", "Type", "Bool", "->", "eo::List", "eo::List::cons", "eo::List::nil", "as"}:
            return
        # Literal families remain syntax; arithmetic operations have a separate hook.
        if name in {"eo::to_bin", "eo::to_str", "eo::var"} or name.startswith(("#b", "#x")) or name.lstrip("-").isdigit() or "/" in name and all(x.lstrip("-").isdigit() for x in name.split("/")):
            return
        decl = self.decls.get(name)
        if not decl:
            n.error(f"unknown symbol {name}")
        fs = seq(decl)
        kind = atom(fs[0])
        if kind not in {"declare-const", "declare-parameterized-const"}:
            n.error(f"{name} is not a constructor")
        ty = fs[2] if kind == "declare-const" else fs[3]
        expected = len(seq(ty)) - 2 if ty.kind == "list" and atom(seq(ty)[0]) == "->" else 0
        # Unapplied symbols and overloaded declarations are needed in generic
        # operator/type patterns. Saturated monomorphic calls retain arity checks.
        if arity and name not in self.overloaded and not self.attributes(name) and kind == "declare-const" and arity != expected:
            n.error(f"{name}: expected exactly {expected} arguments, got {arity}")
        self.used_symbols.add(name)

    def pattern(self, n, scope):
        if n.kind == "symbol" and n.value in scope:
            return f"(PVar {scope[n.value]})"
        n = self.expand(n)
        if n.kind == "string":
            return f"(PSymbol {quoted(chr(34) + n.value + chr(34))})"
        fs = seq(n) if n.kind == "list" else (n,)
        if not fs:
            n.error("empty pattern")
        name = atom(fs[0])
        if name == "_":
            return apply_ir(self.pattern(fs[1], scope), [self.pattern(a, scope) for a in fs[2:]], "PApply")
        if name not in scope:
            self.symbol(fs[0], len(fs)-1)
        head = f"(PVar {scope[name]})" if name in scope else f"(PSymbol {quoted(name)})"
        args = list(fs[1:])
        nil = self.nil_node(name)
        if nil is not None and args:
            tail = args.pop() if args[-1].kind == "symbol" and atom(args[-1]) in self.list_vars else nil
            result = self.pattern(tail, scope)
            for a in reversed(args):
                result = f"(PApply (PApply {head} {self.pattern(a, scope)}) {result})"
            return result
        return apply_ir(head, [self.pattern(a, scope) for a in args], "PApply")

    def expression(self, n, scope):
        if n.kind == "symbol" and n.value in scope:
            return f"(EVar {scope[n.value]})"
        n = self.expand(n)
        if n.kind == "string":
            return f"(ESymbol {quoted(chr(34) + n.value + chr(34))})"
        fs = seq(n) if n.kind == "list" else (n,)
        if not fs:
            n.error("empty expression")
        name, args = atom(fs[0]), list(fs[1:])
        if name == "eo::define":
            if len(args) != 2:
                n.error("eo::define needs bindings and body")
            n = self.freshen(n, set(scope), [0])
            fs = seq(n)
            pairs = [seq(b) for b in seq(fs[1])]
            # EO let bindings are parallel parser substitutions, not strict
            # evaluations: unused failures and failures in unchosen branches
            # must not be forced.
            subs = {atom(b[0]): b[1] for b in pairs}
            return self.expression(self.substitute(fs[2], subs), scope)
        primitives = {"eo::is_ok": ("EIsOk", 1), "eo::is_eq": ("EIsEq", 2), "eo::eq": ("EEq", 2), "eo::ite": ("EIf", 3),
                      "eo::requires": ("ERequires", 3), "eo::typeof": ("ETypeof", 1)}
        if name in primitives:
            self.natives.add(name)
            constructor, count = primitives[name]
            if len(args) != count:
                n.error(f"{name} expects {count} arguments")
            return f"({constructor} {' '.join(self.expression(a, scope) for a in args)})"
        if name.startswith("eo::") and name not in {"eo::List", "eo::List::nil", "eo::List::cons"}:
            primitive = name[4:]
            known = set("is_ok is_eq hash nameof cmp log is_z is_q is_bin is_str is_bool is_var nil cons list_len list_concat list_nth list_find list_erase list_erase_all list_rev list_setof list_minclude list_meq list_diff list_inter list_singleton_elim list_singleton_intro list_repeat not and or xor add neg mul pow zdiv zmod qdiv is_neg gt len concat extract find to_z to_q to_bin to_str dt_constructors dt_selectors var as".split())
            if primitive not in known:
                n.error(f"unsupported native operation {name}")
            self.natives.add(name)
            return f"(ENative {quoted(name)} {lst([self.expression(a, scope) for a in args])})"
        decl = self.decls.get(name)
        if decl and atom(seq(decl)[0]) == "program":
            saved = self.list_vars.copy()
            count = self.compile_program(name)
            self.list_vars = saved
            if len(args) != count:
                n.error(f"{name}: expected {count} arguments, got {len(args)}")
            return f"(ECall {quoted(name)} {lst([self.expression(a, scope) for a in args])})"
        if name == "_":
            return apply_ir(self.expression(args[0], scope), [self.expression(a, scope) for a in args[1:]], "EApply")
        if name not in scope:
            self.symbol(fs[0], len(args))
        head = f"(EVar {scope[name]})" if name in scope else f"(ESymbol {quoted(name)})"
        nil = self.nil_node(name)
        if nil is not None and args:
            tail = args.pop() if args[-1].kind == "symbol" and atom(args[-1]) in self.list_vars else nil
            result = self.expression(tail, scope)
            for a in reversed(args):
                result = f"(EApply (EApply {head} {self.expression(a, scope)}) {result})"
            return result
        return apply_ir(head, [self.expression(a, scope) for a in args], "EApply")

    def compile_program(self, name):
        if name in self.programs:
            return self.programs[name][0]
        decl = self.decls[name]
        fs = seq(decl)
        scope, bs, explicit = self.binders(fs[2])
        if len(fs) != 7 or atom(fs[3]) != ":signature":
            decl.error(f"{name}: expected a program signature and case body")
        inputs = [self.type_pattern(t, scope) for t in seq(fs[4])]
        output = self.type_pattern(fs[5], scope)
        self.programs[name] = (len(inputs), None)
        cases = []
        for case in seq(fs[6]):
            pair = seq(case)
            if len(pair) != 2:
                case.error("program case must have pattern and body")
            lhs = seq(pair[0])
            if not lhs or atom(lhs[0]) != name or len(lhs) != len(inputs) + 1:
                case.error(f"invalid case head/arity for {name}")
            pats = [self.pattern(p, scope) for p in lhs[1:]]
            body = self.expression(pair[1], scope)
            cases.append(f"{{| case_patterns := {lst(pats)}; case_body := {body} |}}")
        if not cases:
            decl.error("program has no cases")
        code = (f"{{| program_binders := {bs}; program_inputs := {lst(inputs)}; "
                f"program_output := {output}; program_cases := {lst(cases)} |}}")
        self.programs[name] = (len(inputs), code)
        return len(inputs)

    def compile_rule(self, name):
        decl = self.decls.get(name)
        if not decl or atom(seq(decl)[0]) != "declare-rule":
            raise SignatureError(f"unknown rule {name}")
        fs = seq(decl)
        scope, bs, _ = self.binders(fs[2])
        fields, i = {}, 3
        while i < len(fs):
            k = atom(fs[i])
            if k not in {":args", ":premises", ":premise-list", ":requires", ":conclusion"}:
                fs[i].error(f"unsupported rule field {k}")
            if k in fields:
                fs[i].error(f"duplicate rule field {k}")
            count = 2 if k == ":premise-list" else 1
            if i+count >= len(fs):
                decl.error("malformed rule field")
            fields[k] = fs[i+1:i+count+1]
            i += count+1
        if ":conclusion" not in fields:
            decl.error("missing :conclusion")
        if ":premises" in fields and ":premise-list" in fields:
            decl.error("conflicting premise declarations")
        args = [self.pattern(p, scope) for p in seq(fields[":args"][0])] if ":args" in fields else []
        prems = [self.pattern(p, scope) for p in seq(fields[":premises"][0])] if ":premises" in fields else []
        premise_op = "None"
        if ":premise-list" in fields:
            pat, op = fields[":premise-list"]
            if self.nil_node(atom(op)) is None:
                op.error("premise-list operator needs :right-assoc-nil")
            self.used_symbols.add(atom(op))
            prems = [self.pattern(pat, scope)]
            premise_op = f"(Some {quoted(atom(op))})"
        reqs = []
        if ":requires" in fields:
            for req in seq(fields[":requires"][0]):
                pair = seq(req)
                if len(pair) != 2:
                    req.error("requirement must be an expression pair")
                reqs.append(f"({self.expression(pair[0], scope)}, {self.expression(pair[1], scope)})")
        conclusion = self.expression(fields[":conclusion"][0], scope)
        self.rules[name] = (f"{{| rule_binders := {bs}; rule_arguments := {lst(args)}; "
                            f"rule_premises := {lst(prems)}; rule_premise_list := {premise_op}; rule_requires := {lst(reqs)}; "
                            f"rule_conclusion := {conclusion} |}}")

    def compile(self, selected):
        if not selected or len(set(selected)) != len(selected):
            raise SignatureError("select a nonempty, duplicate-free list of rules")
        for name in sorted(selected):
            self.compile_rule(name)
        rules = "[" + ";\n   ".join(f"({quoted(n)}, {self.rules[n]})" for n in sorted(self.rules)) + "]"
        programs = "[" + ";\n   ".join(f"({quoted(n)}, {self.programs[n][1]})" for n in sorted(self.programs)) + "]"
        operators = []
        # Closed nils are executable metadata. Dependent nils are recorded as
        # unavailable; reaching one fails closed until the generic typed-nil hook.
        for name in sorted(self.used_symbols | {"eo::List::cons"}):
            nil = self.nil_node(name)
            if nil is not None:
                if nil.kind == "symbol" and (nil.value in self.decls or nil.value in {"true", "false", "eo::List::nil"}):
                    operators.append(f"({quoted(name)}, Symbol {quoted(nil.value)})")
        operator_code = lst(operators)
        closed_ops = {name for name in self.used_symbols | {"eo::List::cons"}
                      if self.nil_node(name) is not None and self.nil_node(name).kind == "symbol"}
        blocked, binary = [], []
        for name in sorted(self.decls):
            attrs = self.attributes(name)
            if not attrs:
                continue
            tags = {atom(a) for a in attrs if a.kind == "symbol" and atom(a).startswith(":")}
            if tags <= {":chainable", ":right-assoc", ":left-assoc"}:
                binary.append(name)
            elif tags != {":right-assoc-nil"} or name not in closed_ops:
                blocked.append(name)
        blocked_code = lst(map(quoted, blocked))
        binary_code = lst(map(quoted, binary))
        aliases = []
        for name, decl in sorted(self.decls.items()):
            fs = seq(decl)
            if atom(fs[0]) == "define" and not seq(fs[2]) and fs[3].kind == "symbol":
                target = self.expand(fs[3])
                if target.kind == "symbol":
                    aliases.append((name, atom(target)))
        alias_code = lst([f"({quoted(a)}, Symbol {quoted(b)})" for a, b in aliases])
        inverse_code = lst([f"({quoted(b)}, Symbol {quoted(a)})" for a, b in aliases])
        code = ("(* Generated by tools/eunoia/compile.py; syntax computation only. *)\n"
                "From Stdlib Require Import String List.\n"
                "From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime.\n"
                "Import ListNotations.\nOpen Scope string_scope.\n\n"
                f"Definition cpc_blocked_operators : list string := {blocked_code}.\n"
                f"Definition cpc_binary_operators : list string := {binary_code}.\n"
                f"Definition cpc_aliases : list (string * term) := {alias_code}.\n"
                f"Definition cpc_surface_names : list (string * term) := {inverse_code}.\n\n"
                f"Definition cpc_operators : list (string * term) := {operator_code}.\n\n"
                f"Definition cpc_programs : list (string * program) :=\n  {programs}.\n\n"
                f"Definition cpc_rules : list (string * rule) :=\n  {rules}.\n\n"
                "Definition derive_with (extra : primitive_hook) (fuel : nat) (typeof : term -> option term)\n"
                "    (name : string) (args premises : list term) : option term :=\n"
                "  let canon := rename_symbols cpc_aliases in\n"
                "  let surface := rename_symbols cpc_surface_names in\n"
                "  if forallb (surface_supported cpc_blocked_operators cpc_binary_operators) (map canon (args ++ premises)) then\n"
                "  option_map surface (run_surface_rule_with extra fuel\n"
                "    (fun t => option_map canon (typeof (surface t)))\n"
                "    cpc_operators cpc_programs cpc_rules name (map canon args) (map canon premises)) else None.\n\n"
                "Definition derive := derive_with no_extension.\n")
        all_rules = sorted(n for n, d in self.decls.items() if atom(seq(d)[0]) == "declare-rule")
        manifest = {
            "format": 2,
            "scope": "explicit subset; excluded rules are unavailable at runtime",
            "selected_rules": sorted(self.rules),
            "excluded_rules": sorted(set(all_rules) - set(self.rules)),
            "programs": sorted(self.programs),
            "expanded_definitions": sorted(self.definitions),
            "native_operations": sorted(self.natives),
            "unsupported_attributed_operators": blocked,
            "binary_only_attributed_operators": binary,
            "constructors": sorted(self.used_symbols),
            "sources": {str(p.relative_to(self.root.parent)) if p.is_relative_to(self.root.parent)
                        else str(p): h for p, h in self.files.items()},
            "generated_sha256": hashlib.sha256(code.encode()).hexdigest(),
        }
        return code, manifest


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("signature", type=Path)
    ap.add_argument("--rules", nargs="+", required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--manifest", type=Path, required=True)
    args = ap.parse_args(argv)
    try:
        code, manifest = Compiler(args.signature).compile(args.rules)
        # Do all parsing/compilation before opening any output file.
        args.output.write_text(code)
        args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    except (SignatureError, OSError, RecursionError) as ex:
        print(f"signature compilation failed: {ex}", file=sys.stderr)
        return 2
    print(f"compiled {len(manifest['selected_rules'])} rules, {len(manifest['programs'])} helpers; "
          f"{len(manifest['excluded_rules'])} rules explicitly excluded", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
