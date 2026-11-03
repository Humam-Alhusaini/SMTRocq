#!/usr/bin/env python3
"""Fail-closed, fixed-arity Eunoia signature to Rocq data compiler.

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
        for b in seq(n):
            parts = seq(b)
            if len(parts) not in (2, 3):
                b.error("unsupported binder shape")
            name = atom(parts[0])
            if name in scope:
                b.error(f"duplicate binder {name}")
            implicit = len(parts) == 3
            if implicit and (atom(parts[2]) != ":implicit" or atom(parts[1]) != "Type"):
                b.error("only :implicit Type binders supported; :list/:opaque rejected")
            ty = self.type_pattern(parts[1], scope)
            ident = len(scope)
            scope[name] = ident
            types.append(f"({ident}, {ty})")
            if not implicit:
                explicit.append(parts[0])
        return scope, lst(types), explicit

    def type_pattern(self, n, scope):
        # Deliberately exclude dependent, function, quote and parameterized types.
        name = atom(n)
        if name in scope:
            return f"(PVar {scope[name]})"
        if name in self.overloaded:
            n.error(f"overloaded type {name} requires unsupported resolution")
        if name not in {"Type", "Bool"}:
            decl = self.decls.get(name)
            if not decl or len(seq(decl)) != 3 or atom(seq(decl)[0]) != "declare-const" or atom(seq(decl)[2]) != "Type":
                n.error(f"unsupported atomic type {name}")
            self.used_symbols.add(name)
        return f"(PSymbol {quoted(name)})"

    def symbol(self, n, arity):
        name = atom(n)
        if name in self.overloaded:
            n.error(f"overloaded constructor {name} requires unsupported resolution")
        if name in {"true", "false", "Type", "Bool"}:
            if arity:
                n.error("builtin literal/type applied as a function")
            return
        decl = self.decls.get(name)
        if not decl:
            n.error(f"unknown symbol {name}")
        fs = seq(decl)
        kind = atom(fs[0])
        if kind == "declare-const":
            ty, attrs, scope = fs[2], fs[3:], {}
        elif kind == "declare-parameterized-const":
            if len(fs) < 4:
                decl.error("incomplete parameterized constant")
            scope, _, explicit = self.binders(fs[2])
            if explicit:
                decl.error("explicit parameterized constants unsupported")
            ty, attrs = fs[3], fs[4:]
        else:
            n.error(f"{name} is not a first-order constructor")
        if ty.kind == "list":
            ts = seq(ty)
            if not ts or atom(ts[0]) != "->" or len(ts) < 3:
                ty.error("unsupported constructor type")
            for t in ts[1:]:
                self.type_pattern(t, scope)
            expected = len(ts) - 2
        else:
            self.type_pattern(ty, scope)
            expected = 0
        # These attributes have ordinary binary behavior at exactly arity 2.
        # N-ary nil, binder, arg-list, and other attributes always reject.
        valid = not attrs or (expected == arity == 2 and (
            (len(attrs) == 1 and atom(attrs[0]) in {":left-assoc", ":right-assoc"}) or
            (len(attrs) == 2 and atom(attrs[0]) == ":chainable" and atom(attrs[1]) == "and")))
        if not valid:
            n.error(f"unsupported constructor attributes on {name}")
        if arity != expected:
            n.error(f"{name}: expected exactly {expected} arguments, got {arity}")
        self.used_symbols.add(name)

    def pattern(self, n, scope):
        if n.kind == "symbol" and n.value in scope:
            return f"(PVar {scope[n.value]})"
        if n.kind == "list":
            fs = seq(n)
            if not fs:
                n.error("empty pattern")
            if atom(fs[0]) in scope:
                n.error("variable-headed patterns unsupported")
            self.symbol(fs[0], len(fs) - 1)
            return apply_ir(f"(PSymbol {quoted(atom(fs[0]))})",
                            [self.pattern(a, scope) for a in fs[1:]], "PApply")
        self.symbol(n, 0)
        return f"(PSymbol {quoted(atom(n))})"

    def expression(self, n, scope):
        if n.kind == "symbol" and n.value in scope:
            return f"(EVar {scope[n.value]})"
        fs = seq(n) if n.kind == "list" else (n,)
        if not fs:
            n.error("empty expression")
        name, args = atom(fs[0]), fs[1:]
        if name in scope:
            n.error("variable-headed applications unsupported")
        if name == "eo::define":
            if len(args) != 2 or len(seq(args[0])) != 1:
                n.error("eo::define supports exactly one binding")
            binding = seq(seq(args[0])[0])
            if len(binding) != 2:
                n.error("malformed eo::define binding")
            var = atom(binding[0])
            if var in scope:
                n.error("eo::define shadowing unsupported")
            ident = len(scope)
            value = self.expression(binding[1], scope)
            body = self.expression(args[1], dict(scope, **{var: ident}))
            return f"(ELet {ident} {value} {body})"
        primitives = {"eo::eq": ("EEq", 2), "eo::ite": ("EIf", 3),
                      "eo::requires": ("ERequires", 3), "eo::typeof": ("ETypeof", 1)}
        if name in primitives:
            constructor, count = primitives[name]
            if len(args) != count:
                n.error(f"{name} expects {count} arguments")
            return f"({constructor} {' '.join(self.expression(a, scope) for a in args)})"
        if name.startswith("eo::"):
            n.error(f"unsupported native operation {name}")
        decl = self.decls.get(name)
        if decl and atom(seq(decl)[0]) in {"program", "define"}:
            count = self.compile_program(name)
            if len(args) != count:
                n.error(f"{name}: expected {count} arguments, got {len(args)}")
            return f"(ECall {quoted(name)} {lst([self.expression(a, scope) for a in args])})"
        self.symbol(fs[0], len(args))
        return apply_ir(f"(ESymbol {quoted(name)})",
                        [self.expression(a, scope) for a in args], "EApply")

    def compile_program(self, name):
        if name in self.programs:
            return self.programs[name][0]
        decl = self.decls[name]
        fs = seq(decl)
        scope, bs, explicit = self.binders(fs[2])
        if atom(fs[0]) == "define":
            # A define's return type is inferred by Ethos. We require a
            # concrete program signature for runtime input/output type checks.
            decl.error("define helpers require desugaring to a typed program")
        if len(fs) != 7 or atom(fs[3]) != ":signature":
            decl.error(f"{name}: expected a program signature and case body")
        inputs = [self.type_pattern(t, scope) for t in seq(fs[4])]
        output = self.type_pattern(fs[5], scope)
        self.programs[name] = (len(inputs), None)  # recursive references
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
        fields = {}
        rest = fs[3:]
        if len(rest) % 2:
            decl.error("unsupported rule flag or malformed field list")
        order = []
        for key, value in zip(rest[::2], rest[1::2]):
            k = atom(key)
            if k not in {":args", ":premises", ":requires", ":conclusion"}:
                key.error(f"unsupported rule field {k}")
            if k in fields:
                key.error(f"duplicate rule field {k}")
            fields[k] = value
            order.append(k)
        if ":conclusion" not in fields:
            decl.error("missing :conclusion")
        if order != sorted(order, key=[":premises", ":args", ":requires", ":conclusion"].index):
            decl.error("rule fields are out of Eunoia order")
        args = [self.pattern(p, scope) for p in seq(fields[":args"])] if ":args" in fields else []
        prems = [self.pattern(p, scope) for p in seq(fields[":premises"])] if ":premises" in fields else []
        reqs = []
        if ":requires" in fields:
            for req in seq(fields[":requires"]):
                pair = seq(req)
                if len(pair) != 2:
                    req.error("requirement must be an expression pair")
                reqs.append(f"({self.expression(pair[0], scope)}, {self.expression(pair[1], scope)})")
        conclusion = self.expression(fields[":conclusion"], scope)
        self.rules[name] = (f"{{| rule_binders := {bs}; rule_arguments := {lst(args)}; "
                            f"rule_premises := {lst(prems)}; rule_requires := {lst(reqs)}; "
                            f"rule_conclusion := {conclusion} |}}")

    def compile(self, selected):
        if not selected or len(set(selected)) != len(selected):
            raise SignatureError("select a nonempty, duplicate-free list of rules")
        for name in sorted(selected):
            self.compile_rule(name)
        rules = "[" + ";\n   ".join(f"({quoted(n)}, {self.rules[n]})" for n in sorted(self.rules)) + "]"
        programs = "[" + ";\n   ".join(f"({quoted(n)}, {self.programs[n][1]})" for n in sorted(self.programs)) + "]"
        code = ("(* Generated by tools/eunoia/compile.py; syntax computation only. *)\n"
                "From Stdlib Require Import String List.\n"
                "From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime.\n"
                "Import ListNotations.\nOpen Scope string_scope.\n\n"
                f"Definition cpc_programs : list (string * program) :=\n  {programs}.\n\n"
                f"Definition cpc_rules : list (string * rule) :=\n  {rules}.\n\n"
                "Definition derive (fuel : nat) (typeof : term -> option term)\n"
                "    (name : string) (args premises : list term) : option term :=\n"
                "  run_rule fuel typeof cpc_programs cpc_rules name args premises.\n")
        all_rules = sorted(n for n, d in self.decls.items() if atom(seq(d)[0]) == "declare-rule")
        manifest = {
            "format": 1,
            "scope": "explicit subset; excluded rules are unavailable at runtime",
            "selected_rules": sorted(self.rules),
            "excluded_rules": sorted(set(all_rules) - set(self.rules)),
            "programs": sorted(self.programs),
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
