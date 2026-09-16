#!/usr/bin/env python3
"""Frozen-policy proof evaluation with independently frozen statement retrieval."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_repair_pilot as pilot
from tools.proof_retrieved_context import render
from harness.runner import run_cmd


def validate_contexts(manifest_bytes, metadata, contexts, tasks):
    if hashlib.sha256(manifest_bytes).hexdigest() != metadata['manifest_sha256']:
        raise ValueError('retrieval contexts belong to a different frozen manifest')
    if set(contexts) != {task['id'] for task in tasks}:
        raise ValueError('retrieval task coverage mismatch')
    for context in contexts.values():
        if context.get('reference_fragment_used') is not False:
            raise ValueError('retrieval must explicitly exclude reference fragments')
        for path, expected in context.get('library_sha256', {}).items():
            if hashlib.sha256(Path(path).read_bytes()).hexdigest() != expected:
                raise ValueError('retrieved library changed after freeze')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--contexts', type=Path, required=True)
    p.add_argument('--model-path', type=Path, required=True)
    p.add_argument('--resume', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--device', default='mps')
    p.add_argument('--max-tokens', type=int, default=512)
    p.add_argument('--seconds', type=int, default=400)
    p.add_argument('--seed', type=int, default=20260912)
    p.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    a = p.parse_args()
    if not 1 <= a.max_tokens <= 1024 or not 30 <= a.seconds <= 900:
        p.error('invalid bounded generation/time budget')
    a.output = a.output.resolve()
    a.manifest = a.manifest.resolve()
    a.contexts = a.contexts.resolve()
    a.rounds = 1
    a.split = 'development'
    a.include_dependencies = True
    a.verifier_timeout = 30
    if a.worker:
        contexts = json.loads(a.contexts.read_text())
        metadata = json.loads(a.contexts.with_name('config.json').read_text())
        tasks = pilot.selected_tasks(json.loads(a.manifest.read_text()), a.split)
        validate_contexts(a.manifest.read_bytes(), metadata, contexts, tasks)
        original_prompt = pilot.prompt_for
        # Scoped to this isolated worker. Candidate assembly/checking remains
        # byte-identical; only the model's context is extended.
        pilot.prompt_for = lambda task, feedback=None: original_prompt(task, feedback) + render(contexts[task['id']])
        (a.output/'contexts.json').write_bytes(a.contexts.read_bytes())
        (a.output/'context-config.json').write_text(json.dumps(metadata, indent=2))
        pilot.worker(a)
        return
    a.output.mkdir(parents=True, exist_ok=False)
    (a.output/'context-evaluator.py').write_bytes(Path(__file__).read_bytes())
    (a.output/'base-evaluator.py').write_bytes(Path(pilot.__file__).read_bytes())
    (a.output/'manifest.json').write_bytes(a.manifest.read_bytes())
    command = [sys.executable, '-u', str(Path(__file__).resolve()), *sys.argv[1:], '--worker']
    code, output, elapsed, timed_out = run_cmd(command, ROOT, a.seconds)
    (a.output/'console.log').write_text(output)
    (a.output/'execution.json').write_text(json.dumps(dict(exit_code=code, elapsed_seconds=elapsed, timed_out=timed_out), indent=2))
    print(output[-5000:])
    raise SystemExit(0 if code == 0 and not timed_out else 1)


if __name__ == '__main__':
    main()
