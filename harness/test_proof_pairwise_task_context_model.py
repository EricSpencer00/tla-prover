from tools.proof_pairwise_task_context_model import (
    feature_vector, fit_pairwise, score)


def test_task_context_changes_representation_without_candidate_index():
    candidate = "BY SMT DEF Init, Next"
    first = feature_vector(candidate, "Visible statement-only context:\nInit == theorem\nNext == theorem\n")
    second = feature_vector(candidate, "Visible statement-only context:\nTypeOK == theorem\n")
    assert first != second
    assert len(first) == 19


def test_pairwise_signal_prefers_positive_action():
    prompt = "Visible statement-only context:\nInit == theorem\nNext == theorem\n"
    good = feature_vector("BY SMT DEF Init, Next", prompt)
    bad = feature_vector("OBVIOUS", prompt)
    weights = fit_pairwise([[a - b for a, b in zip(good, bad)]] * 4)
    assert score(weights, good) > score(weights, bad)
