import json

from tools import protected_paired_inference as runner


def test_grammar_arm_uses_enforced_structured_output_transport(tmp_path, monkeypatch):
    receipt = {
        "status": "inputs_recovered",
        "budget": {
            "rows": [47, 107], "generations_per_row": 2,
            "arms": ["existing_decoder", "grammar_enforced"],
            "max_new_tokens": 1024, "item_seconds": 45,
            "sany_seconds": 30, "seed": 20261011,
            "parameter_updates": 0, "gate_claim": False,
        },
        "packet": {"sha256": runner.sha(b"packet")},
        "rows": {str(row): {"prompt_sha256": runner.sha(f"prompt-{row}")}
                 for row in runner.ROWS},
    }
    packet = tmp_path / "packet.bin"
    packet.write_bytes(b"packet")
    input_receipt = tmp_path / "input.json"
    input_receipt.write_text(json.dumps(receipt))
    grammar = tmp_path / "grammar.ebnf"
    grammar.write_text('root ::= "ok"\n')

    class PacketTools:
        @staticmethod
        def selected(_):
            return ({row: [{"prompt": f"prompt-{row}"}] for row in runner.ROWS}, None)

    monkeypatch.setitem(__import__("sys").modules, "tools.proof_fullmodule_multiexample_probe", PacketTools)
    seen = []

    def fake_post(_base, body, _timeout):
        seen.append(body)
        return {"choices": [{"message": {"content": "ok"}, "finish_reason": "stop"}]}

    monkeypatch.setattr(runner, "post", fake_post)
    runner.run(type("Args", (), {
        "output": str(tmp_path / "out"), "input_receipt": str(input_receipt),
        "packet": str(packet), "grammar": str(grammar),
        "base_url": "http://test/v1", "model": "test",
    })())

    constrained = [body for body in seen if "structured_outputs" in body]
    assert len(constrained) == 4
    assert all(body["structured_outputs"] == {"grammar": 'root ::= "ok"\n'}
               for body in constrained)
    assert all("extra_body" not in body for body in constrained)


def test_structural_repair_intervention_preserves_base_prompt_hash(tmp_path, monkeypatch):
    prompt = "frozen prompt"
    receipt = {
        "status": "inputs_recovered",
        "budget": {
            "rows": [47, 107], "generations_per_row": 2,
            "arms": ["existing_decoder", "grammar_enforced"],
            "max_new_tokens": 1024, "item_seconds": 45,
            "sany_seconds": 30, "seed": 20261011,
            "parameter_updates": 0, "gate_claim": False,
        },
        "packet": {"sha256": runner.sha(b"packet")},
        "rows": {str(row): {"prompt_sha256": runner.sha(prompt)}
                 for row in runner.ROWS},
    }
    packet = tmp_path / "packet.bin"
    packet.write_bytes(b"packet")
    input_receipt = tmp_path / "input.json"
    input_receipt.write_text(json.dumps(receipt))
    grammar = tmp_path / "grammar.ebnf"
    grammar.write_text('root ::= "ok"\n')

    class PacketTools:
        @staticmethod
        def selected(_):
            return ({row: [{"prompt": prompt}] for row in runner.ROWS}, None)

    monkeypatch.setitem(__import__("sys").modules, "tools.proof_fullmodule_multiexample_probe", PacketTools)
    monkeypatch.setattr(runner, "post", lambda *_args: {
        "choices": [{"message": {"content": "ok"}, "finish_reason": "stop"}]
    })
    result = runner.run(type("Args", (), {
        "output": str(tmp_path / "out"), "input_receipt": str(input_receipt),
        "packet": str(packet), "grammar": str(grammar),
        "base_url": "http://test/v1", "model": "test",
        "prompt_intervention": "declaration_schema",
    })())
    assert result["prompt_intervention"] == "declaration_schema"
    assert all(record["base_prompt_sha256"] == runner.sha(prompt)
               for record in result["records"])


def test_output_template_intervention_has_explicit_module_boundaries():
    suffix = runner.OUTPUT_TEMPLATE_SUFFIX
    assert "---- MODULE <name> ----" in suffix
    assert "====` as the final line" in suffix
    assert "[x \\in S |-> expr]" in suffix
    assert "escaped newlines" in suffix


def test_declaration_commas_intervention_targets_parseable_variable_declarations():
    suffix = runner.DECLARATION_COMMAS_SUFFIX
    assert "VARIABLES a, b, c" in suffix
    assert "one bare identifier per line" in suffix
    assert "SPECIFICATION == Init" in suffix


def test_canonical_syntax_intervention_targets_operator_and_section_forms():
    suffix = runner.CANONICAL_SYNTAX_SUFFIX
    assert "never `IN`" in suffix
    assert "never write " in suffix
    assert "SPECIFICATION ==`" in suffix


def test_let_boundary_intervention_forbids_invalid_definition_separators():
    suffix = runner.LET_BOUNDARY_SUFFIX
    assert "each ending with `==`" in suffix
    assert "never use semicolons" in suffix
    assert "exactly one `IN` expression" in suffix


def test_compact_module_intervention_is_recorded_and_has_single_next_guard(tmp_path, monkeypatch):
    prompt = "frozen prompt"
    receipt = {
        "status": "inputs_recovered",
        "budget": {
            "rows": [47, 107], "generations_per_row": 2,
            "arms": ["existing_decoder", "grammar_enforced"],
            "max_new_tokens": 1024, "item_seconds": 45,
            "sany_seconds": 30, "seed": 20261011,
            "parameter_updates": 0, "gate_claim": False,
        },
        "packet": {"sha256": runner.sha(b"packet")},
        "rows": {str(row): {"prompt_sha256": runner.sha(prompt)}
                 for row in runner.ROWS},
    }
    packet = tmp_path / "packet.bin"
    packet.write_bytes(b"packet")
    input_receipt = tmp_path / "input.json"
    input_receipt.write_text(json.dumps(receipt))
    grammar = tmp_path / "grammar.ebnf"
    grammar.write_text('root ::= "ok"\n')

    class PacketTools:
        @staticmethod
        def selected(_):
            return ({row: [{"prompt": prompt}] for row in runner.ROWS}, None)

    monkeypatch.setitem(__import__("sys").modules, "tools.proof_fullmodule_multiexample_probe", PacketTools)
    monkeypatch.setattr(runner, "post", lambda *_args: {
        "choices": [{"message": {"content": "ok"}, "finish_reason": "stop"}]
    })
    result = runner.run(type("Args", (), {
        "output": str(tmp_path / "out"), "input_receipt": str(input_receipt),
        "packet": str(packet), "grammar": str(grammar),
        "base_url": "http://test/v1", "model": "test",
        "prompt_intervention": "compact_module",
    })())
    assert result["prompt_intervention"] == "compact_module"
    assert "exactly one Next" in runner.COMPACT_MODULE_SUFFIX
    assert all(record["base_prompt_sha256"] == runner.sha(prompt)
               for record in result["records"])


def test_module_body_schema_targets_embedded_expression_and_duplicate_sections():
    suffix = runner.MODULE_BODY_SCHEMA_SUFFIX
    assert "exact module-body shape" in suffix
    assert "never put EVALUATE" in suffix
    assert "Do not repeat SPECIFICATION" in suffix
    assert "finish immediately with `====`" in suffix
