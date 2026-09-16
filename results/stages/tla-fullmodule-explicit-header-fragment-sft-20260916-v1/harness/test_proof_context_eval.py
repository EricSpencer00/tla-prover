import hashlib
import pytest
from tools.proof_context_eval import validate_contexts


def test_manifest_and_task_coverage_are_fixed():
    metadata = dict(manifest_sha256=hashlib.sha256(b'manifest').hexdigest())
    contexts = {'one': dict(reference_fragment_used=False)}
    validate_contexts(b'manifest', metadata, contexts, [dict(id='one')])
    with pytest.raises(ValueError):
        validate_contexts(b'other', metadata, contexts, [dict(id='one')])
    with pytest.raises(ValueError):
        validate_contexts(b'manifest', metadata, contexts, [dict(id='two')])


def test_mutated_library_rejected(tmp_path):
    library = tmp_path/'L.tla'
    library.write_text('first')
    contexts = {'one': dict(reference_fragment_used=False,
        library_sha256={str(library):hashlib.sha256(library.read_bytes()).hexdigest()})}
    library.write_text('changed')
    with pytest.raises(ValueError):
        validate_contexts(b'm', dict(manifest_sha256=hashlib.sha256(b'm').hexdigest()), contexts, [dict(id='one')])
