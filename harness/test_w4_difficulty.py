"""Tests for the W4 difficulty probe. No network, no Java, no model calls."""
from __future__ import annotations

import json
import unittest
from pathlib import Path

from . import w4_corpus, w4_difficulty as wd


def _row(key, arm="safety", tier="gold", nl="NL text", module="W4Od1m1p1t1"):
    """A minimally-shaped graded corpus row."""
    return {
        "seed_key": key,
        "arm": arm,
        "tier_name": tier,
        "nl": nl,
        "module": module,
        "spec_text": f"---- MODULE {module} ----\n====",
        "cfg_text": "INIT Init\nNEXT Next\nINVARIANT Inv",
        "property_invariant": "Inv",
    }


def _corpus(counts):
    """counts: {(arm, tier): n} -> a list of distinctly-keyed rows."""
    rows = []
    for (arm, tier), n in sorted(counts.items()):
        for i in range(n):
            rows.append(_row(f"w4opus::{arm}-{tier}-{i:04d}", arm=arm, tier=tier))
    return rows


class TestLargestRemainder(unittest.TestCase):
    def test_sums_to_n_exactly(self):
        for n in (1, 7, 300, 999):
            alloc = wd._largest_remainder({"a": 1000, "b": 500, "c": 3}, n)
            self.assertEqual(sum(alloc.values()), n, f"n={n}")

    def test_caps_at_stratum_size_and_rehomes(self):
        # "c" can absorb at most 2; the other 298 must land elsewhere.
        alloc = wd._largest_remainder({"a": 1000, "b": 500, "c": 2}, 300)
        self.assertLessEqual(alloc["c"], 2)
        self.assertEqual(sum(alloc.values()), 300)

    def test_rehoming_survives_several_tiny_strata(self):
        # One pass of capping is not enough here: capping "c" pushes rows into
        # "d", which then also overflows.
        alloc = wd._largest_remainder({"a": 10, "b": 8, "c": 1, "d": 1}, 20)
        self.assertEqual(sum(alloc.values()), 20)
        for s, size in {"a": 10, "b": 8, "c": 1, "d": 1}.items():
            self.assertLessEqual(alloc[s], size)

    def test_n_larger_than_corpus_clamps(self):
        alloc = wd._largest_remainder({"a": 5, "b": 3}, 100)
        self.assertEqual(sum(alloc.values()), 8)

    def test_empty_and_zero(self):
        self.assertEqual(wd._largest_remainder({}, 10), {})
        self.assertEqual(wd._largest_remainder({"a": 5}, 0), {"a": 0})

    def test_deterministic_under_dict_reordering(self):
        a = wd._largest_remainder({"a": 7, "b": 7, "c": 7}, 10)
        b = wd._largest_remainder({"c": 7, "b": 7, "a": 7}, 10)
        self.assertEqual(a, b)


class TestSelectSample(unittest.TestCase):
    def setUp(self):
        self.rows = _corpus({
            ("safety", "diamond"): 500,
            ("safety", "gold"): 3000,
            ("safety", "silver"): 600,
            ("safety", "bronze"): 90,
            ("liveness", "diamond"): 90,
            ("liveness", "gold"): 460,
            ("liveness", "silver"): 7,
        })

    def test_exact_size(self):
        self.assertEqual(len(wd.select_sample(self.rows, n=300)), 300)

    def test_deterministic_under_seed(self):
        a = [r["seed_key"] for r in wd.select_sample(self.rows, n=300, seed=7)]
        b = [r["seed_key"] for r in wd.select_sample(self.rows, n=300, seed=7)]
        self.assertEqual(a, b)

    def test_different_seed_draws_differently(self):
        a = [r["seed_key"] for r in wd.select_sample(self.rows, n=300, seed=7)]
        b = [r["seed_key"] for r in wd.select_sample(self.rows, n=300, seed=8)]
        self.assertNotEqual(a, b)

    def test_input_order_does_not_change_the_draw(self):
        shuffled = list(reversed(self.rows))
        a = [r["seed_key"] for r in wd.select_sample(self.rows, n=300)]
        b = [r["seed_key"] for r in wd.select_sample(shuffled, n=300)]
        self.assertEqual(a, b)

    def test_every_stratum_above_the_rounding_threshold_is_represented(self):
        picked = wd.select_sample(self.rows, n=300)
        strata = {wd.stratum_of(r) for r in picked}
        for s in [("safety", "diamond"), ("safety", "gold"), ("safety", "silver"),
                  ("safety", "bronze"), ("liveness", "diamond"), ("liveness", "gold")]:
            self.assertIn(s, strata)

    def test_a_stratum_thinner_than_one_slot_rounds_to_zero(self):
        # liveness/silver is 7 of 4,747 rows here (0.15%); at n=300 its exact
        # quota is 0.44. Proportional allocation is kept PURE -- no minimum
        # floor -- because forcing a slot biases the pooled estimate and a `p`
        # from one or two samples has no resolution anyway. The omission has to
        # be visible, not corrected.
        picked = wd.select_sample(self.rows, n=300)
        self.assertNotIn(("liveness", "silver"), {wd.stratum_of(r) for r in picked})

    def test_unsampled_strata_are_recorded_in_the_manifest(self):
        import tempfile
        picked = wd.select_sample(self.rows, n=300)
        with tempfile.TemporaryDirectory() as td:
            m = wd.freeze_sample(picked, Path(td) / "s.json", n=300,
                                 corpus_rows=self.rows)
        self.assertIn("liveness/silver", m["strata_unsampled"])

    def test_no_duplicates(self):
        picked = wd.select_sample(self.rows, n=300)
        keys = [r["seed_key"] for r in picked]
        self.assertEqual(len(keys), len(set(keys)))

    def test_rejects_ungraded_rows(self):
        bad = [{"seed_key": "w4opus::x", "nl": "n"}]
        with self.assertRaises(ValueError) as cm:
            wd.select_sample(bad, n=1)
        self.assertIn("ungraded", str(cm.exception))

    def test_adding_a_tier_does_not_reshuffle_existing_strata(self):
        before = {r["seed_key"] for r in wd.select_sample(self.rows, n=300)
                  if wd.stratum_of(r) == ("liveness", "diamond")}
        widened = self.rows + _corpus({("safety", "platinum"): 200})
        after = {r["seed_key"] for r in wd.select_sample(widened, n=300)
                 if wd.stratum_of(r) == ("liveness", "diamond")}
        # Allocation shifts, so the sets differ in size; the point is that the
        # per-stratum RNG is keyed on the stratum, so the smaller draw is a
        # PREFIX-stable subset rather than an unrelated reshuffle.
        self.assertTrue(after <= before or before <= after)


class TestFreezeAndLoad(unittest.TestCase):
    def setUp(self):
        self.rows = _corpus({("safety", "gold"): 50, ("liveness", "gold"): 10})
        self.picked = wd.select_sample(self.rows, n=20)

    def test_manifest_shape(self, ):
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "sample_frozen.json"
            m = wd.freeze_sample(self.picked, p, n=20)
            self.assertEqual(m["n_selected"], 20)
            self.assertEqual(sum(m["strata_counts"].values()), 20)
            self.assertEqual(m["sha256"], wd.sample_sha256(m["seed_keys"]))
            self.assertEqual(json.loads(p.read_text())["sha256"], m["sha256"])

    def test_hash_is_order_independent(self):
        keys = [r["seed_key"] for r in self.picked]
        self.assertEqual(wd.sample_sha256(keys),
                         wd.sample_sha256(list(reversed(keys))))

    def test_load_roundtrip(self):
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "sample_frozen.json"
            wd.freeze_sample(self.picked, p, n=20)
            manifest, rows = wd.load_sample(p, rows=self.rows)
            self.assertEqual(len(rows), 20)
            self.assertEqual([r["seed_key"] for r in rows], manifest["seed_keys"])

    def test_load_rejects_tampered_hash(self):
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "sample_frozen.json"
            wd.freeze_sample(self.picked, p, n=20)
            m = json.loads(p.read_text())
            m["seed_keys"] = m["seed_keys"][:-1]
            p.write_text(json.dumps(m))
            with self.assertRaises(ValueError) as cm:
                wd.load_sample(p, rows=self.rows)
            self.assertIn("sha256", str(cm.exception))

    def test_load_rejects_corpus_drift(self):
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "sample_frozen.json"
            wd.freeze_sample(self.picked, p, n=20)
            shrunk = [r for r in self.rows
                      if r["seed_key"] != self.picked[0]["seed_key"]]
            with self.assertRaises(ValueError) as cm:
                wd.load_sample(p, rows=shrunk)
            self.assertIn("no longer in the corpus", str(cm.exception))


class TestProbePrompt(unittest.TestCase):
    def setUp(self):
        self.row = _row("w4opus::d1-m1-p1-t1", nl="A system.\nSAFETY PROPERTY: nothing bad.",
                        module="W4Od1m1p1t1")

    def test_generation_mode_is_byte_identical_to_w2_loop(self):
        from .w2_loop import generation_prompt
        self.assertEqual(
            wd.probe_prompt(self.row, "generation"),
            generation_prompt(self.row["nl"], self.row["module"]),
        )

    def test_generation_prompt_carries_the_contract_the_corpus_was_verified_under(self):
        p = wd.probe_prompt(self.row, "generation")
        self.assertIn("W4Od1m1p1t1", p)
        self.assertIn("PROPERTY_INVARIANT", p)
        self.assertIn("```cfg", p)

    def test_sft_user_mode_is_what_corpus_prep_actually_renders(self):
        # Pins the claim rather than asserting it: extract the user turn from
        # the real SFT rendering and require probe_prompt to reproduce it.
        from .corpus_prep import to_harmony_sft
        rendered = to_harmony_sft(self.row, fmt="chatml")["text"]
        user_turn = rendered.split("<|im_start|>user\n", 1)[1].split("<|im_end|>", 1)[0]
        self.assertEqual(wd.probe_prompt(self.row, "sft_user"), user_turn)

    def test_the_two_modes_differ__this_is_the_finding(self):
        # If this ever passes as equal, corpus_prep was fixed to train on the
        # generation contract -- at which point the secondary arm is redundant
        # and the probe's primary mode should be revisited. Failing loudly is
        # the point.
        gen = wd.probe_prompt(self.row, "generation")
        sft = wd.probe_prompt(self.row, "sft_user")
        self.assertNotEqual(gen, sft)
        self.assertNotIn("PROPERTY_INVARIANT", sft)
        self.assertNotIn(self.row["module"], sft)

    def test_sft_target_drops_the_property_invariant_line(self):
        from .corpus_prep import _target_block
        self.assertNotIn("PROPERTY_INVARIANT", _target_block(self.row))

    def test_rejects_unknown_mode(self):
        with self.assertRaises(ValueError):
            wd.probe_prompt(self.row, "framing_a")

    def test_rejects_row_without_nl_or_module(self):
        with self.assertRaises(ValueError):
            wd.probe_prompt({**self.row, "nl": ""}, "generation")
        with self.assertRaises(ValueError):
            wd.probe_prompt({**self.row, "module": ""}, "generation")

    def test_prompt_sha_is_stable_and_discriminating(self):
        p = wd.probe_prompt(self.row, "generation")
        self.assertEqual(wd.prompt_sha256(p), wd.prompt_sha256(p))
        self.assertNotEqual(wd.prompt_sha256(p),
                            wd.prompt_sha256(wd.probe_prompt(self.row, "sft_user")))


class TestAgainstRealCorpus(unittest.TestCase):
    """Integration: the real 5,010-row export. Skipped when shards are absent
    (forks, CI checkouts without the ledgers)."""

    @classmethod
    def setUpClass(cls):
        if not list(Path("results/runs").glob("w4-opus-shard*")):
            raise unittest.SkipTest("no w4-opus-shard* dirs in this checkout")
        cls.rows = w4_corpus.grade_corpus(w4_corpus.load_effective())

    def test_sample_is_300_and_stable(self):
        a = wd.select_sample(self.rows, n=300)
        b = wd.select_sample(self.rows, n=300)
        self.assertEqual(len(a), 300)
        self.assertEqual([r["seed_key"] for r in a], [r["seed_key"] for r in b])

    def test_no_excluded_keys_selected(self):
        excluded = set(w4_corpus.load_exclusions().get("excluded_seed_keys", []))
        picked = {r["seed_key"] for r in wd.select_sample(self.rows, n=300)}
        self.assertEqual(picked & excluded, set())

    def test_every_picked_row_has_the_fields_the_probe_needs(self):
        for r in wd.select_sample(self.rows, n=300):
            self.assertTrue(r.get("nl"), r["seed_key"])
            self.assertTrue(r.get("spec_text"), r["seed_key"])
            self.assertTrue(r.get("cfg_text"), r["seed_key"])

    def test_liveness_arm_is_represented(self):
        picked = wd.select_sample(self.rows, n=300)
        n_live = sum(1 for r in picked if r["arm"] == "liveness")
        # 567/5010 = 11.3% of the corpus; proportional allocation should land
        # near 34. Loose bounds -- this guards against the arm vanishing, not
        # against a rounding shift.
        self.assertGreater(n_live, 20, "liveness arm nearly absent from sample")
        self.assertLess(n_live, 50)


if __name__ == "__main__":
    unittest.main()
