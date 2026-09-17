from tools.proof_factorized_action_model import features, fit, score


def test_features_are_factorized_and_do_not_depend_on_candidate_index():
    prompt = "Visible statement-only context:\nSetExtensionality == theorem\n"
    first = features("BY SMT, SetExtensionality", prompt)
    second = features("BY SMT, SetExtensionality", prompt)
    assert first == second
    assert first[8] > 0
    assert len(first) == 10


def test_factorized_model_can_separate_synthetic_actions():
    prompt = "Visible statement-only context:\n"
    good = features("BY SMT DEF Init", prompt)
    bad = features("OBVIOUS", prompt)
    weights = fit([(good, 1), (bad, 0), (good, 1), (bad, 0)])
    assert score(weights, good) > score(weights, bad)
