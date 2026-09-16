"""CPU-only admission for the structure-first planner generation contract."""

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_structure_first_sft_train as worker


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--probe', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()

    packet, rows = worker.load_packet(args.packet)
    probe, structures = worker.load_probe(args.probe)
    checks = []
    for row in worker.REFERENCE_ROWS:
        structure = structures[row]
        plan = worker.plan_text(structure['module_name'], structure)
        parsed = worker.parse_plan(plan, structure['module_name'])
        expected = [part['id'] if part['kind'] == 'operator' else part['kind']
                    for part in structure['parts']]
        actual = [part['id'] for part in parsed]
        if actual != expected:
            raise ValueError(f'canonical plan mismatch at row {row}')
        if not plan.startswith(worker.PLAN_PREFIX + structure['module_name'] + '\n'):
            raise ValueError(f'planner prefix mismatch at row {row}')
        if not plan.endswith(worker.PLAN_STOP):
            raise ValueError(f'planner stop mismatch at row {row}')
        checks.append(dict(row=row, module_name=structure['module_name'],
                          part_count=len(parsed), plan_sha256=file_sha_bytes(plan)))

    result = dict(
        schema=1,
        kind='fullmodule_structure_first_planner_cpu_admission_v1',
        packet_sha256=file_sha(args.packet),
        probe_sha256=file_sha(args.probe),
        reference_count=len(checks),
        canonical_plans_exact=True,
        planner_prefix_exact=True,
        planner_stop_exact=True,
        forced_prefix_enabled=worker.BUDGET['planner_forced_prefix'],
        forced_eos_suffix=worker.BUDGET['planner_forced_eos_after'],
        model_weights_loaded=False,
        cuda_touched=False,
        optimizer_updates=0,
        training_authorized=False,
        quality_claim=False,
        model_improvement_claim=False,
        gate_claim=False,
        proof_claim=False,
        checks=checks,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(admission='pass', references=len(checks),
                          output_sha256=file_sha(args.output)), sort_keys=True))


def file_sha_bytes(value):
    return hashlib.sha256(value.encode()).hexdigest()


if __name__ == '__main__':
    main()
