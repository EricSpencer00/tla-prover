from tools.proof_action_signature_independent_score import normalize_rankings


def test_normalize_signature_rankings_uses_distance_and_frozen_candidates():
    packet = {"rows": [{"id": "task", "candidate_proposals": ["BY SMT", "BY SMT DEF x"]}]}
    rankings = {"task": [
        {"candidate_index": 1, "candidate": "BY SMT DEF x", "signature_distance": 0.1},
        {"candidate_index": 0, "candidate": "BY SMT", "signature_distance": 1.1},
    ]}
    result = normalize_rankings(rankings, packet)
    assert [row["candidate_index"] for row in result["task"]] == [1, 0]
