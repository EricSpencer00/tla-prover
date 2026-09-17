from tools.proof_multistep_structural_action_control import structural_key


def test_structural_order_prefers_explicit_backend_definitions():
    candidates = [
        "BY SMT", "BY SMT DEF Init, Next", "BY DEF Init, Next",
        "BY SMT, SetExtensionality",
    ]
    ordered = sorted(range(4), key=lambda i: structural_key(candidates[i], i))
    assert ordered == [1, 2, 3, 0]


def test_structural_order_has_stable_index_tiebreak():
    assert structural_key("BY SMT", 2) > structural_key("BY SMT", 1)
