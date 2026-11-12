#!/usr/bin/env python3
"""Compile corrupted actual source declarations as isolated test modules.

Pinned source bytes are never edited. Every replacement must occur exactly
once, and the full selected signature is used so syntax metadata is unchanged.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from compile import Compiler, parse

ROOT = Path(__file__).resolve().parents[3]
MUTATIONS = [
    ('IntEqPremiseMutated', 'arith-int-eq-conflict',
     ':premises ((= (= (to_real (to_int c1)) c1) false))',
     ':premises ((= (= (to_real (to_int c1)) c1) true))'),
    ('IntEqResultMutated', 'arith-int-eq-conflict',
     ':conclusion (= (= (to_real t1) c1) false)',
     ':conclusion (= (= (to_real t1) c1) true)'),
    ('IntGeqPremiseMutated', 'arith-int-geq-tighten',
     '(= cc1 (+ (to_int c1) 1))', '(= cc1 (+ (to_int c1) 2))'),
    ('IntGeqResultMutated', 'arith-int-geq-tighten',
     ':conclusion (= (>= (to_real t1) c1) (>= t1 cc1))',
     ':conclusion (= (>= (to_real t1) c1) (> t1 cc1))'),
    ('IntFloorMutated', '$run_evaluate',
     '(($run_evaluate (to_int x))   (eo::to_z ($run_evaluate x)))',
     '(($run_evaluate (to_int x))   (eo::neg (eo::to_z ($run_evaluate x))))'),
    ('IntCastMutated', '$run_evaluate',
     '(($run_evaluate (to_real x))  (eo::to_q ($run_evaluate x)))',
     '(($run_evaluate (to_real x))  (eo::to_z ($run_evaluate x)))'),
    ('IntPolyGuardMutated', '$is_poly_norm_rel_consts',
     '(eo::not (eo::or (eo::eq (eo::to_q cx) 0/1) (eo::eq (eo::to_q cy) 0/1)))',
     '(eo::or (eo::eq (eo::to_q cx) 0/1) (eo::eq (eo::to_q cy) 0/1))'),
]


def mutated_compiler(name, old, new):
    compiler = Compiler(ROOT / 'tools/eunoia/signatures/cpc/Cpc.eo')
    decl = compiler.decls[name]
    source = decl.path.read_text()
    assert source.count(old) == 1, (name, old)
    forms = parse(source.replace(old, new), decl.path)
    compiler.decls[name] = next(n for n in forms if n.kind == 'list'
        and len(n.value) > 1 and n.value[1].value == name and len(n.value) == len(decl.value))
    return compiler


if __name__ == '__main__':
    rules = (ROOT / 'tools/eunoia/rules.txt').read_text().split()
    for module, name, old, new in MUTATIONS:
        code, _ = mutated_compiler(name, old, new).compile(rules)
        (Path(sys.argv[1]) / (module + '.v')).write_text(code)
