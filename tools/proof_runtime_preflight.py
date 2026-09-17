#!/usr/bin/env python3
"""Fail-closed TLAPS runtime gate for proof jobs.

Runs a known-good and a known-false theorem through the exact configured
tlapm binary and library path before a training job is allowed to start.
"""
import argparse
import hashlib
import json
import os
import subprocess
import tempfile
import re
import socket
from pathlib import Path


GOOD = """---- MODULE RuntimeGood ----
EXTENDS Naturals, TLAPS
THEOREM Good == 1 + 1 = 2
OBVIOUS
====
"""
BAD = """---- MODULE RuntimeFalse ----
EXTENDS Naturals, TLAPS
THEOREM FalseClaim == 1 = 2
BY SMT
====
"""


def control_passed(rc, output, expected):
    if rc is None or rc < 0 or re.search(
            r'assertion|exception|segmentation|not found|No such file|Permission denied|timeout|interrupted',
            output, re.I):
        return False
    if expected:
        matches = re.findall(r'^\s*(?:\[INFO\]: )?All ([1-9]\d*) obligations? proved\.?\s*$', output, re.M)
        # TLAPS 1.5.0 emits this benign Zenon diagnostic while processing its
        # zero-obligation TLAPS.tla support module, before proving the actual
        # control. Preserve fail-closed behavior for every other error.
        benign = re.sub(r'Zenon error: exhausted search space', '', output)
        return rc == 0 and len(matches) == 1 and not re.search(r'failed|omitted|error', benign, re.I)
    return bool(rc in (0, 1, 3) and
                re.search(r'\[ERROR\]: [1-9]\d*/[1-9]\d* obligations? failed\.', output) and
                '[ERROR]: Could not prove or check:' in output)


def run(binary: Path, library: str, source: str, name: str, timeout: int):
    with tempfile.TemporaryDirectory(prefix="tla-runtime-preflight-") as d:
        work = Path(d)
        target = work / f"{name}.tla"
        target.write_text(source)
        includes = sum((['-I', p] for p in library.split(':') if p), [])
        env = dict(os.environ)
        env.setdefault('PROVE_TLA_TLAPM_LEGACY', '1')
        try:
            flags = ['--threads', '1'] if os.environ.get('PROVE_TLA_TLAPM_LEGACY') == '1' else ['--strict', '--cache-dir', str(work / '.tlacache')]
            p = subprocess.run([str(binary), *flags, '--nofp', *includes, target.name], cwd=work,
                               env=env, text=True, capture_output=True,
                               timeout=timeout)
            output = p.stdout + p.stderr
            return p.returncode, output
        except (OSError, subprocess.TimeoutExpired) as e:
            return None, str(e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tlapm', required=True, type=Path)
    ap.add_argument('--library', required=True)
    ap.add_argument('--receipt', required=True, type=Path)
    ap.add_argument('--timeout', type=int, default=30)
    a = ap.parse_args()
    if not a.tlapm.is_file() or not os.access(a.tlapm, os.X_OK):
        raise SystemExit('PREFLIGHT FAIL: tlapm is not executable')
    records = []
    for kind, source, expected in [('known_good', GOOD, True),
                                   ('known_false', BAD, False)]:
        rc, output = run(a.tlapm, a.library, source,
                         'RuntimeGood' if expected else 'RuntimeFalse', a.timeout)
        passed = control_passed(rc, output, expected)
        records.append({'control': kind, 'returncode': rc, 'passed': passed,
                        'output': output, 'source': source,
                        'output_sha256': hashlib.sha256(output.encode()).hexdigest()})
    result = {'schema': 1, 'hostname': socket.gethostname(), 'library': a.library, 'tlapm': str(a.tlapm), 'tlapm_sha256': hashlib.sha256(a.tlapm.read_bytes()).hexdigest(),
              'controls': records, 'passed': all(r['passed'] for r in records)}
    a.receipt.parent.mkdir(parents=True, exist_ok=True)
    a.receipt.write_text(json.dumps(result, indent=2) + '\n')
    if not result['passed']:
        raise SystemExit('PREFLIGHT FAIL: same-node TLAPS controls did not pass')
    print('PREFLIGHT PASS: known-good succeeds and known-false is rejected')


if __name__ == '__main__':
    main()
