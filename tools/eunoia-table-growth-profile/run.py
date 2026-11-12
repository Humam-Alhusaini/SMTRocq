#!/usr/bin/env python3
"""Bounded, sequential probes of unchanged public theorem files.

Build @install first. The driver records outcomes, including timeouts, and does
not interpret solver or native producer success as theorem acceptance.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
WRAPPER = os.environ.get("EUNOIA_ENV", str(next(p for p in Path(__file__).resolve().parents if (p / "dune-project").is_file()) / "scripts/eunoia/env"))


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifacts():
    installed = ROOT / '_build/install/default/lib'
    return {str(p.relative_to(installed)): digest(p) for p in sorted(installed.rglob('*'))
            if p.suffix in ('.vo', '.cmxs')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--repeat', type=int, default=1)
    parser.add_argument('sources', type=Path, nargs='+')
    args = parser.parse_args()
    if args.timeout <= 0 or args.repeat <= 0:
        parser.error('timeout and repeat must be positive')
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    installed = ROOT / '_build/install/default/lib'
    before = artifacts()
    metadata = {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'branch': subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip(),
                'diff': subprocess.check_output(['git', 'diff'], cwd=ROOT, text=True),
                'search_sha256': digest(ROOT / 'src/eunoia_witness/search.ml'),
                'timeout_s': args.timeout, 'repeat': args.repeat,
                'artifacts_before': before, 'cwd': str(ROOT),
                'settings': {'EUNOIA_TABLE_PROFILE': '1', 'EUNOIA_WITNESS_PROFILE': '1'}}
    write(args.output / 'metadata.json', metadata)
    rows = []
    for iteration in range(args.repeat):
        for number, source in enumerate(args.sources):
            directory = args.output / f'{iteration}-{number}-{source.parent.parent.name}-{source.stem}'
            directory.mkdir()
            copied = directory / source.name
            copied.write_bytes(source.read_bytes())
            command = [WRAPPER, 'rocq', 'c', '-q', '-color', 'no', '-I', str(installed),
                       '-Q', str(installed / 'coq/user-contrib/SMTCoq'), 'SMTCoq', str(copied)]
            environment = dict(os.environ, **metadata['settings'])
            temporary = directory / 'tmp'
            temporary.mkdir()
            environment['TMPDIR'] = str(temporary)
            row = {'source': str(source.resolve()), 'source_sha256': digest(source),
                   'command': command, 'loadavg_before': os.getloadavg(),
                   'cpu_count': os.cpu_count(), 'iteration': iteration}
            usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
            started = time.monotonic()
            with (directory / 'output.log').open('w') as log:
                process = subprocess.Popen(command, cwd=ROOT, env=environment, stdout=log,
                                           stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    process.wait(timeout=args.timeout)
                    row['timeout'] = False
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    row['timeout'] = True
                except BaseException:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    raise
            usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
            row.update(exit_code=process.returncode, wall_s=time.monotonic() - started,
                       user_s=usage_after.ru_utime - usage_before.ru_utime,
                       system_s=usage_after.ru_stime - usage_before.ru_stime,
                       loadavg_after=os.getloadavg(), log=str(directory / 'output.log'),
                       fresh_vo=copied.with_suffix('.vo').exists())
            row['checked_marker'] = 'EUNOIA_BENCH_CHECKED' in (directory / 'output.log').read_text()
            write(directory / 'command.json', row)
            rows.append(row)
            write(args.output / 'results.json', rows)
            print(json.dumps(row), flush=True)
    metadata['artifacts_after'] = artifacts()
    metadata['artifacts_unchanged'] = before == metadata['artifacts_after']
    metadata['search_unchanged'] = metadata['search_sha256'] == digest(ROOT / 'src/eunoia_witness/search.ml')
    write(args.output / 'metadata.json', metadata)
    if not metadata['artifacts_unchanged'] or not metadata['search_unchanged']:
        raise RuntimeError('measured artifacts or search source changed')


if __name__ == '__main__':
    main()
