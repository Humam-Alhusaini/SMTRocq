"""Syntax-only CPC inventory, deliberately not a proof checker or rule evaluator."""

from collections import Counter
from pathlib import Path


def tokens(text):
    """Keep SMT-LIB strings/quoted symbols opaque; ignore semicolon comments."""
    offset = 0
    while offset < len(text):
        char = text[offset]
        if char.isspace():
            offset += 1
        elif char == ";":
            end = text.find("\n", offset)
            offset = len(text) if end < 0 else end + 1
        elif char in "()":
            yield char
            offset += 1
        elif char in ('"', "|"):
            start, quote = offset, char
            offset += 1
            while offset < len(text):
                if text[offset] == quote:
                    offset += 1
                    if quote == '"' and offset < len(text) and text[offset] == '"':
                        offset += 1
                        continue
                    yield text[start:offset]
                    break
                offset += 1
            else:
                raise ValueError("unterminated string or quoted symbol")
        else:
            start = offset
            while offset < len(text) and not text[offset].isspace() and text[offset] not in "();":
                offset += 1
            yield text[start:offset]


def expressions(text):
    """Parse lists iteratively so deep terms do not exhaust Python recursion."""
    result = []
    stack = [result]
    for token in tokens(text):
        if token == "(":
            child = []
            stack[-1].append(child)
            stack.append(child)
        elif token == ")":
            if len(stack) == 1:
                raise ValueError("unmatched closing parenthesis")
            stack.pop()
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise ValueError("unclosed parenthesis")
    return result


def signature_rules(signature):
    """Inventory declarations in the actual include closure; do not evaluate them."""
    base = signature.parent.resolve()
    pending, seen, rules = [signature], set(), {}
    while pending:
        path = pending.pop().resolve()
        if not path.is_relative_to(base):
            raise ValueError(f"signature include escapes CPC tree: {path}")
        if path in seen:
            continue
        seen.add(path)
        for form in expressions(path.read_text()):
            if not isinstance(form, list) or not form:
                continue
            if form[0] == "include":
                if len(form) != 2 or not isinstance(form[1], str) or not form[1].startswith('"'):
                    raise ValueError(f"unsupported include in {path}")
                pending.append(path.parent / form[1][1:-1])
            elif form[0] == "declare-rule":
                name = form[1]
                if name in rules:
                    raise ValueError(f"duplicate rule declaration: {name}")
                rules[name] = {
                    "file": str(path.relative_to(base)),
                    "contains_sorry": ":sorry" in form,
                }
    return rules


def input_logic(text):
    forms = expressions(text)
    # One-shot regression inputs only. Disallow input-side options, get-proof,
    # resets, or additional queries that would make dump provenance ambiguous.
    allowed = {"set-logic", "set-info", "declare-sort", "declare-fun", "declare-const",
               "define-fun", "assert", "check-sat", "exit"}
    for form in forms:
        if (not isinstance(form, list) or not form or
                not isinstance(form[0], str) or form[0] not in allowed):
            raise ValueError("unsupported input command (expected a one-shot QF_UF/QF_LIA input)")
    logics = [form[1:] for form in forms if form[0] == "set-logic"]
    checks = [i for i, form in enumerate(forms) if form[0] == "check-sat"]
    if len(logics) != 1 or logics[0] not in (["QF_UF"], ["QF_LIA"]):
        raise ValueError("expected exactly one QF_UF or QF_LIA set-logic")
    if len(checks) != 1 or forms[checks[0]] != ["check-sat"]:
        raise ValueError("expected exactly one check-sat")
    if forms[checks[0] + 1:] not in ([], [["exit"]]):
        raise ValueError("only exit may follow check-sat")
    if any(form[0] == "exit" for form in forms[:checks[0]]):
        raise ValueError("exit before check-sat")
    return logics[0][0]


def inventory(text, rules):
    forms = expressions(text)
    if len(forms) != 2 or forms[0] != "unsat" or not isinstance(forms[1], list):
        raise ValueError("expected exactly one unsat result and one CPC proof block")
    commands = Counter()
    counts = Counter()
    allowed = {"declare-sort", "declare-const", "define", "assume", "assume-push",
               "step", "step-pop"}
    depth = 0
    for form in forms[1]:
        if (not isinstance(form, list) or not form or
                not isinstance(form[0], str) or form[0] not in allowed):
            raise ValueError("unsupported or malformed CPC command in inventory")
        command = form[0]
        commands[command] += 1
        if command == "assume-push":
            depth += 1
        elif command in ("step", "step-pop"):
            indices = [i for i, item in enumerate(form) if item == ":rule"]
            if len(indices) != 1 or indices[0] + 1 >= len(form):
                raise ValueError("step is missing its unique rule annotation")
            rule = form[indices[0] + 1]
            if not isinstance(rule, str) or rule not in rules:
                raise ValueError(f"rule absent from signature include closure: {rule}")
            if rules[rule]["contains_sorry"]:
                raise ValueError(f"incomplete CPC rule rejected: {rule}")
            counts[rule] += 1
            if command == "step-pop":
                depth -= 1
                if depth < 0:
                    raise ValueError("step-pop without assume-push")
    if depth:
        raise ValueError("unclosed assume-push scope")
    if not counts or not forms[1] or forms[1][-1][:1] != ["step"] or forms[1][-1][2:3] != ["false"]:
        raise ValueError("CPC dump has no explicit final false step")
    return {"commands": dict(sorted(commands.items())),
            "rules": dict(sorted(counts.items())), "steps": sum(counts.values())}
