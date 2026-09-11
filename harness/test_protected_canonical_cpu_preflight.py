from argparse import Namespace
from pathlib import Path

import pytest

from tools import protected_canonical_cpu_preflight as probe


def test_frozen_canonical_grammar_identity_matches_real_artifact():
    grammar = Path('results/runs/syntax-structured-polaris-20260911/job-7605656/canonical-grammar-probe-20260911-v1/canonical.ebnf')
    assert probe.sha(grammar.read_bytes()) == probe.GRAMMAR_SHA


def test_wrong_grammar_fails_before_runtime_import_or_output(tmp_path):
    grammar = tmp_path / 'bad.ebnf'
    grammar.write_text('root ::= "wrong"\n')
    output = tmp_path / 'receipt.json'
    with pytest.raises(ValueError, match='Grammar identity'):
        probe.check(Namespace(grammar=grammar, output=output))
    assert not output.exists()


def test_wrong_packet_fails_before_creating_corpus(tmp_path):
    packet = tmp_path / 'packet.json'
    packet.write_text('{}')
    output = tmp_path / 'corpus.json'
    with pytest.raises(ValueError, match='Packet identity'):
        probe.prepare(Namespace(packet=packet, output=output))
    assert not output.exists()
