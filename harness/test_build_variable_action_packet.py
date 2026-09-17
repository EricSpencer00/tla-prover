from tools.build_variable_action_packet import digest, prompt


def test_prompt_exports_only_statement_context():
    text = prompt({
        "theorem_name": "Inductiveness", "target_goal": "IndAuto => IndAuto'",
        "retrieval": {"visible_facts": [{"name": "TypeOK", "statement": "x \\in Nat"}],
                       "ranked_imported_facts": []},
    })
    assert "TypeOK == x \\in Nat" in text
    assert "reference_fragment" not in text


def test_candidate_digest_is_order_sensitive_at_interface():
    assert digest(["BY SMT", "BY DEF Init"]) != digest(["BY DEF Init", "BY SMT"])
