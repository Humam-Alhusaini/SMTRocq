#!/usr/bin/env python3
"""Compile/recheck the checked replay tactic, with an explicit local-gate source.

Unmerged dependency copies are kept in /tmp and never written to the repository.
Every command and exit code is printed for coordinator reproduction.
"""
import argparse
from pathlib import Path
import shutil
import subprocess

REPO = Path(__file__).resolve().parents[4]
WRAPPER = '/home/charles/code/friends/.toolchains/smtrocq-env'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--local-source', type=Path,
                        default=REPO / 'theories/checker/eunoia/EunoiaLocal.v')
    parser.add_argument('--output', type=Path, default=Path('/tmp/eunoia-backend-validation'))
    args = parser.parse_args()
    if not args.local_source.is_file():
        parser.error('EunoiaLocal is not integrated: supply --local-source explicitly')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if output == REPO or REPO in output.parents:
        parser.error('--output must be outside the repository')
    theory = output / 'eunoia'
    checker = output / 'checker'
    theory.mkdir(exist_ok=True)
    checker.mkdir(exist_ok=True)

    def run(command):
        print('COMMAND:', ' '.join(map(str, command)), flush=True)
        result = subprocess.run(command, cwd=REPO)
        print('EXIT:', result.returncode, flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)

    targets = ['theories',
               '_build/install/default/lib/rocq-smtcoq/META',
               '_build/install/default/lib/rocq-smtcoq/eunoia_frontend/eunoia_frontend.cmxs',
               '_build/install/default/lib/rocq-smtcoq/eunoia_backend/eunoia_backend.cmxs',
               '_build/install/default/lib/rocq-smtcoq/eunoia_backend_test/backend_test_plugin.cmxs']
    run([WRAPPER, 'dune', 'build', *targets])
    base = REPO / '_build/default/theories'
    for source, destination in [(base / 'checker/eunoia', theory), (base / 'checker', checker)]:
        for src in source.glob('*.vo'):
            dst = destination / src.name
            dst.unlink(missing_ok=True)
            shutil.copyfile(src, dst)
    shutil.copyfile(args.local_source, theory / 'EunoiaLocal.v')
    shutil.copyfile(Path(__file__).with_name('Proof.v'), theory / 'Proof.v')
    flags = []
    for path, name in [('utils', 'SMTCoq.utils'), ('structures', 'SMTCoq.structures'),
                       ('checker/fol', 'SMTCoq.checker.fol')]:
        flags += ['-Q', str(base / path), name]
    for name in ['array', 'bva', 'cnf', 'euf', 'lia', 'spl']:
        flags += ['-Q', str(base / 'checker/small-checkers' / name),
                  'SMTCoq.checker.small_checker.' + name]
    flags += ['-Q', str(checker), 'SMTCoq.checker', '-Q', str(theory), 'SMTCoq.checker.eunoia']
    command = [WRAPPER, 'dune', 'exec', '--', 'rocq']
    if args.local_source.resolve() != (REPO / 'theories/checker/eunoia/EunoiaLocal.v').resolve():
        run(command + ['c', *flags, str(theory / 'EunoiaLocal.v')])
        shutil.copyfile(REPO / 'theories/checker/eunoia/EunoiaTactic.v', theory / 'EunoiaTactic.v')
        run(command + ['c', *flags, str(theory / 'EunoiaTactic.v')])
    run(command + ['c', *flags, str(theory / 'Proof.v')])
    run(command + ['check', '-silent', *flags, 'SMTCoq.checker.eunoia.Proof'])


if __name__ == '__main__':
    main()
