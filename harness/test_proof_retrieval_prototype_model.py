from tools.proof_retrieval_prototype_model import candidate_score, cosine, family, tokens


def test_family_and_prompt_signature_are_answer_free():
    assert family("BY SMT DEF Init") == "smt_def"
    assert family("BY DEF Init") == "def"
    assert "init" in tokens("Visible statement-only context:\nInit == theorem\n")


def test_retrieval_score_prefers_supported_similar_family():
    prototypes = [{"family": "smt_def", "tokens": ["init", "next"]}]
    counts = {"smt_def": 1}
    good = candidate_score("BY SMT DEF Init", "Visible statement-only context:\nInit == theorem\n", prototypes, counts)
    bad = candidate_score("BY DEF Init", "Visible statement-only context:\nInit == theorem\n", prototypes, counts)
    assert good > bad
    assert cosine({"init"}, {"init", "next"}) > 0
