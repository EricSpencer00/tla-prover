import unittest

from tools.proof_constrained_action_score import choose


class ConstrainedActionTests(unittest.TestCase):
    def test_neural_choice_cannot_leave_symbolic_shortlist(self):
        shortlist = [
            {"candidate_index": 0, "candidate": "BY SMT"},
            {"candidate_index": 1, "candidate": "BY DEF A"},
            {"candidate_index": 2, "candidate": "BY DEF B"},
            {"candidate_index": 3, "candidate": "BY A"},
        ]
        scores = [
            {"candidate_index": 99, "mean_logp": 100.0},
            {"candidate_index": 2, "mean_logp": -1.0},
            {"candidate_index": 0, "mean_logp": -2.0},
            {"candidate_index": 1, "mean_logp": -3.0},
            {"candidate_index": 3, "mean_logp": -4.0},
        ]
        self.assertEqual(choose(shortlist, scores)["candidate_index"], 2)

    def test_missing_shortlist_score_fails_closed(self):
        shortlist = [{"candidate_index": i, "candidate": str(i)} for i in range(4)]
        scores = [{"candidate_index": i, "mean_logp": -i} for i in range(3)]
        with self.assertRaisesRegex(ValueError, "complete symbolic shortlist"):
            choose(shortlist, scores)


if __name__ == "__main__":
    unittest.main()
