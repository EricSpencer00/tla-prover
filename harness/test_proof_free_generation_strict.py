from tools.proof_free_generation_strict import target_scoped_pass


def certified_record():
    return {
        "certified": True,
        "status": "pass",
        "sany": {"status": "pass"},
        "tlaps": {"status": "pass", "certified": True, "proved": 3, "total": 3},
        "tlaps_diagnostic": {"classification": "proof_success"},
    }


def test_acceptance_requires_sany_and_audited_tlaps_success():
    assert target_scoped_pass(certified_record())


def test_tlaps_looking_record_without_sany_pass_is_rejected():
    result = certified_record()
    result["sany"] = {"status": "model_sany_reject"}
    assert not target_scoped_pass(result)


def test_unmeasured_tlaps_diagnostic_is_rejected():
    result = certified_record()
    result["tlaps_diagnostic"] = {"classification": "unmeasured_unknown"}
    assert not target_scoped_pass(result)
