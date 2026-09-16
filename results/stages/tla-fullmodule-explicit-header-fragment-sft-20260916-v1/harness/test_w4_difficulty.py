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


class _ScriptedModel:
    """Returns replies from a fixed cycle. `n` replies per call, like the real
    OpenAICompatModel (which issues n sequential requests)."""
    id = "scripted-test-model"

    def __init__(self, replies):
        self.replies = list(replies)
        self.calls = []
        self._i = 0

    def generate(self, prompt, n, temperature, max_tokens):
        self.calls.append({"prompt": prompt, "n": n, "temperature": temperature})
        out = []
        for _ in range(n):
            out.append(self.replies[self._i % len(self.replies)])
            self._i += 1
        return out


def _fake_verify(reply, row, workdir, timeout=60):
    """Survives iff the reply says GOOD. No Java, no TLC."""
    ok = "GOOD" in reply
    return {"survived": ok,
            "rejection_reason": None if ok else "scripted_reject",
            "mutation_evidence": "safety_catch" if ok else "no_kill",
            "kill_rate": 0.5 if ok else 0.0,
            "distinct_states": 42}


class TestProbeCell(unittest.TestCase):
    def setUp(self):
        self.row = _row("w4opus::d1-m1-p1-t1")
        self.tmp = __import__("tempfile").TemporaryDirectory()
        self.work = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def test_half_good_gives_p_of_one_half(self):
        m = _ScriptedModel(["GOOD", "BAD"])
        got = wd.probe_cell(m, self.row, k=8, mode="generation",
                            workroot=self.work, verify=_fake_verify)
        self.assertEqual(len(got), 8)
        self.assertEqual(sum(1 for r in got if r["survived"]) / 8, 0.5)

    def test_one_model_call_of_n_not_n_calls(self):
        m = _ScriptedModel(["GOOD"])
        wd.probe_cell(m, self.row, k=8, mode="generation",
                      workroot=self.work, verify=_fake_verify)
        self.assertEqual(len(m.calls), 1)
        self.assertEqual(m.calls[0]["n"], 8)
        self.assertEqual(m.calls[0]["temperature"], wd.TEMPERATURE)

    def test_prompt_matches_the_requested_mode(self):
        m = _ScriptedModel(["GOOD"])
        wd.probe_cell(m, self.row, k=1, mode="sft_user",
                      workroot=self.work, verify=_fake_verify)
        self.assertEqual(m.calls[0]["prompt"], self.row["nl"])

    def test_rows_carry_the_full_schema(self):
        m = _ScriptedModel(["GOOD"])
        got = wd.probe_cell(m, self.row, k=2, mode="generation",
                            workroot=self.work, verify=_fake_verify)
        for r in got:
            for f in ("seed_key", "arm", "tier_name", "mode", "sample_id",
                      "temperature", "survived", "prompt_sha256", "model", "k"):
                self.assertIn(f, r)
            self.assertEqual(r["model"], "scripted-test-model")

    def test_api_error_is_not_scored_as_a_failure(self):
        m = _ScriptedModel(["[api_error 503: not ready]"])
        got = wd.probe_cell(m, self.row, k=4, mode="generation",
                            workroot=self.work, verify=_fake_verify)
        self.assertTrue(all(r["api_error"] for r in got))
        # None, not False -- an outage must not read as "the student failed".
        self.assertTrue(all(r["survived"] is None for r in got))

    def test_skip_samples_are_not_redrawn(self):
        m = _ScriptedModel(["GOOD"])
        got = wd.probe_cell(m, self.row, k=8, mode="generation",
                            workroot=self.work, skip_samples={0, 1, 2},
                            verify=_fake_verify)
        self.assertEqual([r["sample_id"] for r in got], [3, 4, 5, 6, 7])

    def test_workdirs_are_cleaned_up(self):
        m = _ScriptedModel(["GOOD"])
        wd.probe_cell(m, self.row, k=4, mode="generation",
                      workroot=self.work, verify=_fake_verify)
        leftover = [p for p in self.work.rglob("s*") if p.is_dir()]
        self.assertEqual(leftover, [])


class TestRunProbe(unittest.TestCase):
    def setUp(self):
        self.rows = _corpus({("safety", "gold"): 5})
        self.tmp = __import__("tempfile").TemporaryDirectory()
        self.rundir = Path(self.tmp.name) / "run"

    def tearDown(self):
        self.tmp.cleanup()

    def _run(self, model, k=4, **kw):
        return wd.run_probe(model, self.rows, k, "generation", self.rundir,
                            verify=_fake_verify, **kw)

    def test_writes_one_row_per_sample(self):
        s = self._run(_ScriptedModel(["GOOD", "BAD"]), k=4)
        self.assertEqual(s["rows_written"], 20)
        lines = (self.rundir / "rows.jsonl").read_text().splitlines()
        self.assertEqual(len(lines), 20)

    def test_ledger_rows_are_schema_exact(self):
        self._run(_ScriptedModel(["GOOD"]), k=2)
        for line in (self.rundir / "rows.jsonl").read_text().splitlines():
            self.assertEqual(set(json.loads(line)), set(wd.ROW_FIELDS))

    def test_resume_skips_completed_cells(self):
        m1 = _ScriptedModel(["GOOD"])
        self._run(m1, k=4)
        m2 = _ScriptedModel(["GOOD"])
        s2 = self._run(m2, k=4)
        self.assertEqual(s2["cells"], 0)
        self.assertEqual(s2["rows_written"], 0)
        self.assertEqual(len(m2.calls), 0, "resume re-drew an already-done cell")

    def test_resume_redraws_api_error_rows(self):
        # An outage must not be inherited as a completed measurement.
        self._run(_ScriptedModel(["[api_error 503: cold]"]), k=4)
        m2 = _ScriptedModel(["GOOD"])
        s2 = self._run(m2, k=4)
        self.assertEqual(s2["cells"], 5)
        self.assertEqual(s2["survived"], 20)

    def test_api_errors_are_counted_and_surfaced(self):
        s = self._run(_ScriptedModel(["[api_error 500: boom]"]), k=2)
        self.assertEqual(s["api_errors"], 10)

    def test_concurrency_produces_the_same_row_set(self):
        serial = self._run(_ScriptedModel(["GOOD", "BAD"]), k=4)
        rows_serial = sorted((self.rundir / "rows.jsonl").read_text().splitlines())
        self.tearDown()
        self.setUp()
        par = self._run(_ScriptedModel(["GOOD", "BAD"]), k=4, concurrency=4)
        rows_par = sorted((self.rundir / "rows.jsonl").read_text().splitlines())
        self.assertEqual(serial["rows_written"], par["rows_written"])
        self.assertEqual(len(rows_serial), len(rows_par))

    def test_never_writes_outside_its_rundir(self):
        before = sorted(p.name for p in Path("results/runs").glob("w4-opus-shard*")) \
            if Path("results/runs").exists() else []
        self._run(_ScriptedModel(["GOOD"]), k=2)
        after = sorted(p.name for p in Path("results/runs").glob("w4-opus-shard*")) \
            if Path("results/runs").exists() else []
        self.assertEqual(before, after)
        self.assertTrue((self.rundir / "rows.jsonl").exists())


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

    def test_gold_specs_survive_their_own_gate_stack(self):
        """Positive control. Feed each cell's OWN verified spec back as the
        student's reply: it must survive. Without this, a probe that rejects
        everything reports p=0 across the whole corpus and looks like a
        finding. Needs Java + TLC, so it is skipped where those are absent.
        """
        import shutil, tempfile
        if not shutil.which("java"):
            self.skipTest("no java on PATH")
        if not Path("tools/tla2tools.jar").exists():
            self.skipTest("no tools/tla2tools.jar in this checkout")

        _, rows = wd.load_sample("results/runs/w4-difficulty-v1/sample_frozen.json",
                                 rows=self.rows)
        # One per arm -- the liveness path takes require_liveness=True and has
        # its own stutter-strip re-run, which is where it could diverge.
        picks = [next(r for r in rows if r["arm"] == "safety"),
                 next(r for r in rows if r["arm"] == "liveness")]
        for r in picks:
            reply = (f"```tla\n{r['spec_text']}\n```\n"
                     f"```cfg\n{r['cfg_text']}\n```\n"
                     f"PROPERTY_INVARIANT: {r['property_invariant']}\n")
            with tempfile.TemporaryDirectory() as td:
                v = wd.verify_reply(reply, r, Path(td) / "w", timeout=120)
            self.assertTrue(
                v.get("survived"),
                f"{r['arm']} cell {r['seed_key']} did not survive its own gate "
                f"stack (reason={v.get('rejection_reason')}) -- the probe would "
                f"report p=0 everywhere")

    def test_liveness_arm_is_represented(self):
        picked = wd.select_sample(self.rows, n=300)
        n_live = sum(1 for r in picked if r["arm"] == "liveness")
        # 567/5010 = 11.3% of the corpus; proportional allocation should land
        # near 34. Loose bounds -- this guards against the arm vanishing, not
        # against a rounding shift.
        self.assertGreater(n_live, 20, "liveness arm nearly absent from sample")
        self.assertLess(n_live, 50)


def _load_report_tool():
    """tools/ is not a package; load the report module by path."""
    import importlib.util
    p = Path(__file__).resolve().parent.parent / "tools" / "w4_difficulty_report.py"
    spec = importlib.util.spec_from_file_location("w4_difficulty_report", p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class TestIntervalMath(unittest.TestCase):
    """The stdlib Clopper-Pearson / Fisher implementations, against closed
    forms and published values. These are the numbers the decision rule is
    read off, so they get checked rather than trusted."""

    @classmethod
    def setUpClass(cls):
        cls.m = _load_report_tool()

    def test_all_pass_lower_bound_matches_closed_form(self):
        # For k == n the exact CP lower bound is (alpha/2)^(1/n).
        for n in (1, 8, 32, 122, 500):
            lo, hi = self.m.clopper_pearson(n, n)
            self.assertAlmostEqual(lo, 0.025 ** (1.0 / n), places=12, msg=f"n={n}")
            self.assertEqual(hi, 1.0)

    def test_all_fail_upper_bound_matches_closed_form(self):
        for n in (1, 8, 32):
            lo, hi = self.m.clopper_pearson(0, n)
            self.assertEqual(lo, 0.0)
            self.assertAlmostEqual(hi, 1 - 0.025 ** (1.0 / n), places=12)

    def test_textbook_interval(self):
        lo, hi = self.m.clopper_pearson(2, 10)
        self.assertAlmostEqual(lo, 0.02521, places=5)
        self.assertAlmostEqual(hi, 0.55610, places=5)

    def test_interval_contains_the_point_estimate_and_is_ordered(self):
        for n in (5, 32, 300):
            for k in range(n + 1):
                lo, hi = self.m.clopper_pearson(k, n)
                self.assertLessEqual(lo, k / n + 1e-12)
                self.assertLessEqual(k / n - 1e-12, hi)
                self.assertLessEqual(lo, hi)

    def test_k32_all_pass_does_NOT_certify_097(self):
        # This is the arithmetic that invalidated the design doc's original
        # decision rule. If it ever changes, the rule needs rewriting again.
        lo, _ = self.m.clopper_pearson(32, 32)
        self.assertLess(lo, 0.97)
        self.assertAlmostEqual(lo, 0.891119, places=5)

    def test_certifiable_k_for_097_is_122(self):
        k = self.m.saturation_certifiable_k(0.97)
        self.assertEqual(k, 122)
        lo, _ = self.m.clopper_pearson(k, k)
        self.assertGreater(lo, 0.97)
        lo_short, _ = self.m.clopper_pearson(k - 1, k - 1)
        self.assertLess(lo_short, 0.97)

    def test_betainc_endpoints_and_symmetry(self):
        self.assertEqual(self.m.betainc(2, 3, 0.0), 0.0)
        self.assertEqual(self.m.betainc(2, 3, 1.0), 1.0)
        # I_x(a,b) = 1 - I_{1-x}(b,a)
        for a, b, x in ((2, 3, 0.3), (5, 1.5, 0.8), (0.5, 0.5, 0.25)):
            self.assertAlmostEqual(self.m.betainc(a, b, x),
                                   1 - self.m.betainc(b, a, 1 - x), places=10)

    def test_fisher_exact_known_values(self):
        self.assertAlmostEqual(self.m.fisher_exact_two_sided(1, 9, 11, 3),
                               0.0027594, places=6)
        self.assertAlmostEqual(self.m.fisher_exact_two_sided(10, 10, 10, 10),
                               1.0, places=9)

    def test_fisher_never_exceeds_one(self):
        for quad in ((0, 5, 5, 0), (3, 3, 3, 3), (1, 0, 0, 1), (7, 1, 2, 8)):
            self.assertLessEqual(self.m.fisher_exact_two_sided(*quad), 1.0 + 1e-9)


class TestReportRescoring(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.m = _load_report_tool()

    def _ledger(self, specs):
        """specs: [(seed_key, arm, tier, n_pass, n_fail, n_api)] -> rows."""
        rows = []
        for key, arm, tier, npass, nfail, napi in specs:
            i = 0
            for _ in range(npass):
                rows.append({"seed_key": key, "arm": arm, "tier_name": tier,
                             "mode": "generation", "sample_id": i,
                             "survived": True, "api_error": False}); i += 1
            for _ in range(nfail):
                rows.append({"seed_key": key, "arm": arm, "tier_name": tier,
                             "mode": "generation", "sample_id": i,
                             "survived": False, "api_error": False}); i += 1
            for _ in range(napi):
                rows.append({"seed_key": key, "arm": arm, "tier_name": tier,
                             "mode": "generation", "sample_id": i,
                             "survived": None, "api_error": True}); i += 1
        return rows

    def test_bins_are_computed_by_hand_correctly(self):
        rows = self._ledger([
            ("a", "safety", "gold", 8, 0, 0),   # all-pass
            ("b", "safety", "gold", 0, 8, 0),   # never solved
            ("c", "safety", "gold", 3, 5, 0),   # partial
        ])
        cells = self.m.cells_from_rows(rows)
        got = {k[1]: self.m.bin_of(c) for k, c in cells.items()}
        self.assertEqual(got["a"], "all-pass (saturated)")
        self.assertEqual(got["b"], "p=0 (never solved)")
        self.assertEqual(got["c"], "0<p<1 (partial)")

    def test_api_error_rows_leave_the_denominator(self):
        # 4 passes, 0 real failures, 4 outages -> all-pass on n=4, NOT 4/8.
        rows = self._ledger([("a", "safety", "gold", 4, 0, 4)])
        c = self.m.cells_from_rows(rows)[("generation", "a")]
        self.assertEqual((c["n"], c["passes"], c["api_errors"]), (4, 4, 4))
        self.assertEqual(self.m.bin_of(c), "all-pass (saturated)")

    def test_a_cell_of_only_api_errors_is_unmeasured_not_failed(self):
        rows = self._ledger([("a", "safety", "gold", 0, 0, 8)])
        c = self.m.cells_from_rows(rows)[("generation", "a")]
        self.assertEqual(self.m.bin_of(c), "unmeasured")

    def test_report_runs_end_to_end_and_exits_zero(self):
        import io, tempfile
        from contextlib import redirect_stdout
        rows = self._ledger([
            ("a", "safety", "diamond", 8, 0, 0),
            ("b", "safety", "gold", 0, 8, 0),
            ("c", "liveness", "gold", 4, 4, 0),
            ("d", "safety", "gold", 8, 0, 0),
        ])
        with tempfile.TemporaryDirectory() as td:
            rd = Path(td)
            (rd / "rows.jsonl").write_text(
                "\n".join(json.dumps(r) for r in rows) + "\n")
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = self.m.report(rd)
            out = buf.getvalue()
        self.assertEqual(rc, 0)
        self.assertIn("HEADLINE", out)
        self.assertIn("DIAMOND vs GOLD", out)
        self.assertIn("k>=122", out)

    def test_missing_or_empty_ledger_fails_loudly(self):
        import io, tempfile
        from contextlib import redirect_stdout
        with tempfile.TemporaryDirectory() as td:
            buf = io.StringIO()
            with redirect_stdout(buf):
                self.assertEqual(self.m.report(Path(td)), 1)
            (Path(td) / "rows.jsonl").write_text("")
            with redirect_stdout(buf):
                self.assertEqual(self.m.report(Path(td)), 1)


if __name__ == "__main__":
    unittest.main()
