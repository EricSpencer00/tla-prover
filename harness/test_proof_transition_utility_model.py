from tools.proof_transition_utility_model import atom_sequence, fit_logistic, rank


def test_transition_sequence_preserves_order_and_solver_mode():
    tokens = atom_sequence("BY SMT DEF Init, Next, TypeOK")
    assert tokens[:3] == ("solver:smt", "transition:solver:smt->atoms", "length:3")
    assert tokens[-3:] == ("atom:TypeOK", "position:2:TypeOK", "edge:Next->TypeOK")


def test_transition_model_can_prefer_compositional_positive():
    weights, bias = fit_logistic([
        (atom_sequence("BY SMT DEF Init, Next"), 1),
        (atom_sequence("BY SMT"), 0),
        (atom_sequence("BY DEF Init, Next"), 0),
    ], epochs=600, learning_rate=0.1, l2=0.1)
    ranked = rank({}, ["BY SMT", "BY SMT DEF Init, Next"], weights, bias)
    assert ranked[0]["candidate"] == "BY SMT DEF Init, Next"


def test_transition_model_is_candidate_index_free():
    weights, bias = fit_logistic([
        (atom_sequence("BY SMT DEF Init"), 1),
        (atom_sequence("BY SMT"), 0),
    ], epochs=400, learning_rate=0.1)
    first = rank({}, ["BY SMT", "BY SMT DEF Init"], weights, bias)
    second = rank({}, ["BY SMT DEF Init", "BY SMT"], weights, bias)
    assert first[0]["candidate"] == second[0]["candidate"] == "BY SMT DEF Init"
