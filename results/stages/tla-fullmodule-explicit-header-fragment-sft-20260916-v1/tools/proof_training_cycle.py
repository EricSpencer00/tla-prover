#!/usr/bin/env python3
"""One bounded baseline/train/evaluate cycle, preserving every stage artifact."""
import argparse
import json
from pathlib import Path
import sys
import time

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))
from harness.runner import run_cmd


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--model-path', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--steps', type=int, default=32)
    p.add_argument('--lr', type=float, default=5e-5)
    p.add_argument('--device', default='mps')
    p.add_argument('--max-tokens', type=int, default=128)
    p.add_argument('--training-max-tokens', type=int, default=4096)
    p.add_argument('--stage-seconds', type=int, default=600)
    p.add_argument('--include-dependencies', action='store_true')
    a = p.parse_args()
    if not 1 <= a.max_tokens <= 1024 or not 30 <= a.stage_seconds <= 1000:
        p.error('invalid bounded token/time budget')
    a.output = a.output.resolve()
    a.output.mkdir(parents=True, exist_ok=False)
    (a.output/'coordinator.py').write_text(Path(__file__).read_text())
    (a.output/'manifest.json').write_bytes(a.manifest.read_bytes())
    shared = ['--manifest', str(a.manifest.resolve()), '--model-path', str(a.model_path.resolve()),
              '--device', a.device]
    if a.include_dependencies:
        shared.append('--include-dependencies')
    evaluation = [sys.executable, '-u', str(REPO/'tools/proof_repair_pilot.py'), *shared,
                  '--rounds', '1', '--max-tokens', str(a.max_tokens),
                  '--seconds', str(a.stage_seconds), '--seed', '20260912']
    stages = [
        ('before', [*evaluation, '--output', str(a.output/'before')], a.stage_seconds+50),
        ('training', [sys.executable, '-u', str(REPO/'tools/proof_sequence_train.py'), *shared,
                      '--output', str(a.output/'training'), '--steps', str(a.steps),
                      '--seconds', str(a.stage_seconds), '--max-tokens', str(a.training_max_tokens),
                      '--lr', str(a.lr), '--seed', '20260912'], a.stage_seconds+150),
        ('after', [*evaluation, '--output', str(a.output/'after'),
                   '--resume', str(a.output/'training/policy_optimizer.pt')], a.stage_seconds+50)]
    (a.output/'config.json').write_text(json.dumps(dict(stages=stages,
        hypothesis='Response-only multi-token proof SFT improves valid proof-fragment generation on train and source-separated development versus frozen base.',
        stop_condition=f'single fixed {a.steps}-step training batch and matched greedy before/after; no adaptive retry or task removal',
        symbolic_baseline='Evaluate same manifest separately; symbolic results never counted as model outputs'), indent=2))
    started = time.monotonic()
    for label, command, timeout in stages:
        print('STAGE='+label, flush=True)
        code, output, elapsed, timed_out = run_cmd(command, REPO, timeout)
        (a.output/(label+'.log')).write_text(output)
        execution = dict(exit_code=code, elapsed_seconds=elapsed, timed_out=timed_out, command=command)
        (a.output/(label+'-execution.json')).write_text(json.dumps(execution, indent=2))
        print(json.dumps(dict(stage=label, **execution)), flush=True)
        if code != 0 or timed_out:
            raise SystemExit(1)
    summary = {label:json.loads((a.output/label/'summary.json').read_text()) for label,_,_ in stages}
    summary['elapsed_seconds'] = time.monotonic()-started
    (a.output/'summary.json').write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
