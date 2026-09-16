"""Conservatively census saved prover artifacts, including after failed runs."""

from pathlib import Path
import json


def census(result_dir: str | Path, exit_status: int | None = None) -> dict:
    root = Path(result_dir)
    files = []
    if root.exists():
        for path in sorted(p for p in root.rglob("*") if p.is_file()):
            files.append({"path": str(path.relative_to(root)), "size_bytes": path.stat().st_size})
    names = {item["path"] for item in files}
    parent_rows = sorted(n for n in names if n.startswith("restored_parent-row-") and n.endswith(".json"))
    child_rows = sorted(n for n in names if n.startswith("trained_child-row-") and n.endswith(".json"))
    summary_present = bool(names & {"result.json", "summary.json"})
    return {
        "result_dir": str(root),
        "exit_status": exit_status,
        "files": files,
        "checkpoint_created": "policy_optimizer.pt" in names,
        "sany_evaluation_outputs": {"parent": parent_rows, "child": child_rows},
        "sany_evaluation": bool(parent_rows or child_rows),
        "summary_present": summary_present,
        "summary_metrics_unknown": not summary_present,
    }


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("result_dir")
    parser.add_argument("--exit-status", type=int)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    Path(args.output).write_text(json.dumps(census(args.result_dir, args.exit_status), indent=2) + "\n")


if __name__ == "__main__":
    main()
