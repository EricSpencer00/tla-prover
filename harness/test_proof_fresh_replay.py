"""Bounded replay tests: synthetic tasks, fake checkers, no TLAPS execution."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import proof_fresh_replay as replay


class FreshReplayTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.output = Path(self.tmp.name)
        self.tasks = [dict(id=f'task-{i}', prefix='THEOREM Goal == TRUE\n',
                           suffix='\n====\n', theorem_name='Goal', dependencies=[],
                           dependency_sha256={}) for i in range(14)]
        self.arms = {arm: [dict(id=t['id'], fragment='BY SMT',
                               raw_reply_sha256='a'*64) for t in self.tasks]
                     for arm in ('base', 'child')}
        self.now = 0.0
        self.calls = []
        self.snapshots = []

    def attest(self, tasks):
        return dict(runtime=dict(tlapm_path='/fake/tlapm'), inputs_and_code={'f': 'a'*64})

    def checker(self, prefix, fragment, suffix, **kw):
        self.calls.append(kw)
        self.snapshots.append(json.loads((self.output/'summary.json').read_text()))
        return dict(certified=True, status='pass', returncode=0, timed_out=False,
                    proved=1, total=1, output='All 1 obligation proved.\n',
                    command=['/fake/tlapm', '--strict', '--nofp', 'Test.tla'],
                    candidate_path='/fake/Test.tla', sha256='a'*64)

    def run_fake(self, **kw):
        with patch.object(replay, 'bound', return_value=True):
            return replay.evaluate(self.tasks, self.arms, self.output,
                                   checker=kw.pop('checker', self.checker),
                                   attest=kw.pop('attest', self.attest),
                                   clock=lambda: self.now, **kw)

    def summary(self):
        return json.loads((self.output/'summary.json').read_text())

    def test_complete28_paired_order_and_strict_budget(self):
        rows = self.run_fake()
        self.assertEqual([(r['id'], r['arm']) for r in rows],
                         [(t['id'], a) for t in self.tasks for a in ('base', 'child')])
        self.assertEqual(len(self.calls), 28)
        self.assertTrue(all(c['timeout'] == 30 for c in self.calls))
        self.assertTrue(all(c['dependencies'] == () for c in self.calls))
        self.assertEqual(len((self.output/'rows.jsonl').read_text().splitlines()), 28)
        s = self.summary()
        self.assertTrue(s['verification_complete']); self.assertTrue(s['identity_stable'])
        self.assertEqual(s['accounted_attempts'], 28)
        self.assertFalse(s['model_sampling']); self.assertEqual(s['parameter_updates'], 0)
        for arm in ('base', 'child'):
            self.assertEqual(s['per_arm'][arm]['requested_tasks'], 14)
            self.assertEqual(s['per_arm'][arm]['accounted_tasks'], 14)
            self.assertEqual(s['per_arm'][arm]['certified_tasks'], 14)

    def test_interim_summaries_never_certify_completion(self):
        self.run_fake()
        self.assertEqual(len(self.snapshots), 28)
        for s in self.snapshots:
            self.assertFalse(s['verification_complete'])
            self.assertFalse(s['identity_stable'])
            self.assertTrue(all(a['certified_tasks'] == 0 for a in s['per_arm'].values()))

    def test_extraction_rejections_preserve_all28(self):
        self.arms['base'][0]['fragment'] = None
        self.arms['child'][13]['fragment'] = None
        rows = self.run_fake()
        rejected = [r for r in rows if r['status'] == 'extraction_reject']
        self.assertEqual(len(rejected), 2); self.assertEqual(len(self.calls), 26)
        self.assertTrue(all(not r['certified'] for r in rejected))
        self.assertEqual(self.summary()['accounted_attempts'], 28)
        self.assertEqual(self.summary()['per_arm']['base']['certified_tasks'], 13)
        self.assertEqual(self.summary()['per_arm']['child']['certified_tasks'], 13)

    def test_budget_expiry_keeps_unattempted_denominator(self):
        def one_check(*args, **kw):
            row = self.checker(*args, **kw)
            self.now = 1000.0
            return row
        rows = self.run_fake(checker=one_check)
        self.assertEqual(len(self.calls), 1)
        self.assertEqual(sum(r['status'] == 'unmeasured_budget' for r in rows), 27)
        self.assertEqual(self.summary()['accounted_attempts'], 28)
        self.assertTrue(self.summary()['verification_complete'])

    def test_remaining_time_caps_single_check(self):
        def reduced(*args, **kw):
            row = self.checker(*args, **kw)
            self.now = 995.0 if len(self.calls) == 1 else 1000.0
            return row
        self.run_fake(checker=reduced)
        self.assertEqual([c['timeout'] for c in self.calls], [30, 5])

    def test_unknown_and_internal_errors_are_not_model_failures(self):
        def unknown(*args, **kw):
            row = self.checker(*args, **kw)
            row.update(certified=False, status='verifier_reject', returncode=3,
                       total=0, proved=0, output='Unrecognized diagnostic\n')
            if len(self.calls) == 1:
                row['output'] = 'Assertion failed\n'
            return row
        rows = self.run_fake(checker=unknown)
        self.assertEqual(rows[0]['audit']['classification'], 'unmeasured_checker_internal')
        self.assertEqual(rows[1]['audit']['classification'], 'unmeasured_unknown')
        self.assertTrue(all(not r['audit']['measured_model_outcome'] for r in rows))
        self.assertTrue(all(not r['audit']['reward_eligible'] for r in rows))
        self.assertTrue(all(a['certified_tasks'] == 0 for a in self.summary()['per_arm'].values()))

    def test_claimed_success_with_internal_error_cannot_certify(self):
        def contradictory(*args, **kw):
            row = self.checker(*args, **kw)
            row['output'] += 'Assertion failed\n'
            return row
        rows = self.run_fake(checker=contradictory)
        self.assertTrue(all(not r['certified'] for r in rows))
        self.assertTrue(all(a['certified_tasks'] == 0 for a in self.summary()['per_arm'].values()))

    def test_timeout_is_unmeasured(self):
        def timeout(*args, **kw):
            row = self.checker(*args, **kw)
            row.update(certified=False, status='timeout', timed_out=True,
                       returncode=-9, output='timeout')
            return row
        rows = self.run_fake(checker=timeout)
        self.assertTrue(all(r['audit']['classification'] == 'unmeasured_infrastructure' for r in rows))

    def test_runtime_drift_invalidates_completed_ledger(self):
        identity = self.attest(self.tasks)
        changed = copy.deepcopy(identity); changed['inputs_and_code']['f'] = 'b'*64
        with patch.object(replay, 'bound', return_value=True):
            with self.assertRaisesRegex(ValueError, 'identity changed'):
                replay.evaluate(self.tasks, self.arms, self.output, checker=self.checker,
                                attest=unittest.mock.Mock(side_effect=[identity, changed]),
                                clock=lambda: self.now)
        self.assertEqual(self.summary()['accounted_attempts'], 28)
        self.assertFalse(self.summary()['verification_complete'])
        self.assertTrue(all(a['certified_tasks'] == 0 for a in self.summary()['per_arm'].values()))

    def test_in_memory_input_drift_invalidates_ledger(self):
        def mutate(*args, **kw):
            row = self.checker(*args, **kw)
            self.tasks[0]['prefix'] += ' '
            return row
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            self.run_fake(checker=mutate)
        self.assertFalse(self.summary()['verification_complete'])

    def test_unattested_checker_executable_rejected(self):
        def wrong(*args, **kw):
            row = self.checker(*args, **kw)
            row['command'][0] = '/other/tlapm'
            return row
        with self.assertRaisesRegex(ValueError, 'Unattested checker executable'):
            self.run_fake(checker=wrong)
        self.assertFalse(self.summary()['verification_complete'])

    def test_raw_binding_failure_stops_without_claim(self):
        with patch.object(replay, 'bound', side_effect=ValueError('Raw log mismatch')):
            with self.assertRaisesRegex(ValueError, 'Raw log mismatch'):
                replay.evaluate(self.tasks, self.arms, self.output, checker=self.checker,
                                attest=self.attest, clock=lambda: self.now)
        self.assertFalse(self.summary()['verification_complete'])

    def test_full_population_and_order_required(self):
        for alteration in ('short_tasks', 'missing_arm', 'short_rows', 'reordered'):
            with self.subTest(alteration=alteration):
                tasks = copy.deepcopy(self.tasks); arms = copy.deepcopy(self.arms)
                if alteration == 'short_tasks': tasks.pop()
                if alteration == 'missing_arm': del arms['child']
                if alteration == 'short_rows': arms['base'].pop()
                if alteration == 'reordered': arms['base'].reverse()
                with self.assertRaises(ValueError):
                    replay.evaluate(tasks, arms, self.output, checker=self.checker,
                                    attest=self.attest, clock=lambda: self.now)
        self.assertEqual(self.calls, [])


if __name__ == '__main__':
    unittest.main()
