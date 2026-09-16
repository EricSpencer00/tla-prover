import copy
import json
from pathlib import Path
import unittest

from tools import proof_verifier_candidate_rank_cuda_eval as worker


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "results/stages/tla-verifier-candidate-rank-gpu-20260916-v1/packet.json"


class CandidateRankPacketTests(unittest.TestCase):
    def setUp(self):
        self.packet = json.loads(PACKET.read_text())

    def test_packet_is_exact_answer_free_four_row_population(self):
        rows = worker.validate_packet(self.packet)
        self.assertEqual(len(rows), 4)
        self.assertEqual({row["split"] for row in rows}, {"development"})
        self.assertTrue(all(len(row["candidate_proposals"]) >= 4 for row in rows))
        self.assertFalse(self.packet["reference_fragment_used"])
        self.assertFalse(self.packet["tlaps_executed"])

    def test_reference_or_feedback_fields_are_rejected(self):
        mutated = copy.deepcopy(self.packet)
        mutated["rows"][0]["reference_fragment"] = "BY SMT"
        with self.assertRaisesRegex(ValueError, "answer-bearing"):
            worker.validate_packet(mutated)

    def test_candidate_hash_is_bound(self):
        mutated = copy.deepcopy(self.packet)
        mutated["rows"][0]["candidate_proposals"][0] = "BY DEF Init"
        with self.assertRaisesRegex(ValueError, "candidate proposal hash"):
            worker.validate_packet(mutated)


if __name__ == "__main__":
    unittest.main()
