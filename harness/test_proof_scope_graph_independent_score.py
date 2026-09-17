import json

from tools.proof_scope_graph_independent_score import load_scaffolds


def test_score_module_exports_scaffold_loader():
    assert callable(load_scaffolds)


def test_summary_contract_is_non_promotional(tmp_path):
    path = tmp_path / "summary.json"
    path.write_text(json.dumps({"denominator_fixed": True, "quality_claim": False,
                                "gate_claim": False}))
    value = json.loads(path.read_text())
    assert value["denominator_fixed"] and not value["quality_claim"] and not value["gate_claim"]
