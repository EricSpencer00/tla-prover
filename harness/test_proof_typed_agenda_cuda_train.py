from pathlib import Path

from tools import proof_typed_agenda as agenda
from tools import proof_typed_agenda_cuda_train as train


ROOT = Path(__file__).resolve().parents[1]


def test_agenda_head_contract_is_cpu_importable():
    assert train.PROFILE.startswith("frozen bf16")
    assert len(agenda.SLOTS) == 22
    assert all(isinstance(slot, str) for slot in agenda.SLOTS)
