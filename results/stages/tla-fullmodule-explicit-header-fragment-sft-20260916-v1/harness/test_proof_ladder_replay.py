"""Synthetic paired replay: no Java, TLAPS, model, or actual control identity calls."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

from tools import proof_ladder_replay as replay


class LadderReplayTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.output = Path(self.tmp.name)
        self.tasks = [dict(id=f'task-{i}', prefix='THEOREM Goal == TRUE\n', suffix='\n====\n',
                           theorem_name='Goal', dependencies=[], dependency_sha256={}) for i in range(14)]
        self.arms = {a: [dict(id=t['id'], fragment='BY SMT', raw_reply_sha256='a'*64)
                         for t in self.tasks] for a in ('base', 'child')}
        self.now = 0.; self.calls = []; self.interim = []
        self.frozen = dict(controls=dict(runtime=dict(files={})), original={'f': 'a'*64}, code={})

    def checker(self, *args, **kw):
        self.calls.append(kw)
        self.interim.append(self.summary())
        return dict(certified=True, status='pass', sany=dict(status='pass'),
                    tlaps=dict(status='pass'), contract_version=replay.ladder.VERSION)

    def audit(self, task, fragment, result, runtime):
        return dict(certified=result['certified'], sany_status=result['sany']['status'],
                    tlaps_classification='proof_success' if result['certified'] else result['status'])

    def run_fake(self, **kw):
        return replay.evaluate(self.tasks, self.arms, self.output,
            checker=kw.pop('checker', self.checker), audit=kw.pop('audit', self.audit),
            attest=kw.pop('attest', lambda _: copy.deepcopy(self.frozen)), clock=lambda: self.now, **kw)

    def summary(self):
        return json.loads((self.output/'summary.json').read_text())

    def test_full_paired_accounting_no_rewards(self):
        rows = self.run_fake()
        self.assertEqual([(r['id'], r['arm']) for r in rows],
                         [(t['id'], a) for t in self.tasks for a in ('base', 'child')])
        self.assertEqual(len(self.calls), 28)
        self.assertTrue(all(c['timeout'] == 30 for c in self.calls))
        self.assertTrue(all(not r['reward_authorized'] and not r['training_authorized'] for r in rows))
        s = self.summary(); self.assertTrue(s['verification_complete'])
        self.assertEqual(s['accounted_attempts'], 28)
        for a in ('base', 'child'):
            self.assertEqual(s['per_arm'][a]['requested_tasks'], 14)
            self.assertEqual(s['per_arm'][a]['certified_tasks'], 14)
        self.assertTrue(all(not s['verification_complete'] for s in self.interim))
        self.assertTrue(all(a['certified_tasks'] == 0 for s in self.interim for a in s['per_arm'].values()))

    def test_extraction_rejection_keeps_population(self):
        self.arms['base'][0]['fragment'] = None
        rows = self.run_fake()
        self.assertEqual(rows[0]['status'], 'extraction_reject')
        self.assertIsNone(rows[0]['sany']); self.assertIsNone(rows[0]['tlaps'])
        self.assertEqual(len(self.calls), 27); self.assertEqual(len(rows), 28)

    def test_shared_budget_and_remaining_timeout(self):
        def advance(*args, **kw):
            r = self.checker(*args, **kw)
            self.now = 995 if len(self.calls) == 1 else 1000
            return r
        rows = self.run_fake(checker=advance)
        self.assertEqual([c['timeout'] for c in self.calls], [30, 5])
        self.assertEqual(sum(r['status'] == 'unmeasured_budget' for r in rows), 26)
        self.assertEqual(self.summary()['accounted_attempts'], 28)

    def test_unknown_sany_and_contract_statuses_preserved(self):
        statuses = ['unmeasured_unknown', 'unmeasured_checker_internal', 'contract_reject', 'model_sany_reject']
        def reject(*args, **kw):
            r = self.checker(*args, **kw)
            r.update(certified=False, status=statuses[(len(self.calls)-1) % 4])
            r['sany']['status'] = 'model_sany_reject'; r['tlaps'] = None
            return r
        rows = self.run_fake(checker=reject)
        self.assertEqual([r['status'] for r in rows[:4]], statuses)
        self.assertTrue(all(not r['certified'] for r in rows))

    def test_identity_drift_invalidates_final(self):
        changed = copy.deepcopy(self.frozen); changed['code']['new'] = 'b'*64
        with self.assertRaisesRegex(ValueError, 'drift'):
            self.run_fake(attest=Mock(side_effect=[self.frozen, changed]))
        s = self.summary(); self.assertFalse(s['verification_complete'])
        self.assertEqual(s['accounted_attempts'], 28)
        self.assertTrue(all(a['certified_tasks'] == 0 for a in s['per_arm'].values()))

    def test_input_drift_invalidates_final(self):
        def mutate(*args, **kw):
            r = self.checker(*args, **kw); self.tasks[0]['prefix'] += ' '; return r
        with self.assertRaisesRegex(ValueError, 'drift'):
            self.run_fake(checker=mutate)
        self.assertFalse(self.summary()['verification_complete'])

    def test_audit_failure_cannot_complete(self):
        with self.assertRaisesRegex(ValueError, 'tampered'):
            self.run_fake(audit=Mock(side_effect=ValueError('tampered')))
        self.assertFalse(self.summary()['verification_complete'])

    def test_reject_partial_reordered_or_duplicate_population(self):
        for variant in ('short', 'reorder', 'duplicate', 'arm'):
            with self.subTest(variant=variant):
                tasks = copy.deepcopy(self.tasks); arms = copy.deepcopy(self.arms)
                if variant == 'short': tasks.pop()
                if variant == 'reorder': arms['child'].reverse()
                if variant == 'duplicate': tasks[1]['id'] = tasks[0]['id']
                if variant == 'arm': del arms['child']
                with self.assertRaises(ValueError):
                    replay.evaluate(tasks, arms, self.output, checker=self.checker,
                                    attest=lambda _: self.frozen, audit=self.audit)
        self.assertEqual(self.calls, [])

    def test_controls_missing_or_hash_changed_fail_before_identity(self):
        with patch.object(replay.controls, 'identity') as identity:
            with self.assertRaises(FileNotFoundError): replay.admit_controls(self.output)
            (self.output/'rows.json').write_text('[]')
            with self.assertRaises(ValueError): replay.admit_controls(self.output)
            identity.assert_not_called()

    def make_record(self):
        task = self.tasks[0]; fragment = 'BY SMT'
        record = dict(workdir=str(self.output), contract_version=replay.ladder.VERSION,
            certified=False, status='contract_reject', tlaps=None,
            sha256=replay.sha((task['prefix']+fragment+task['suffix']).encode()),
            sany=dict(status='not_run', output='', command=None))
        (self.output/'input.json').write_text(json.dumps(dict(prefix=task['prefix'], fragment=fragment,
            suffix=task['suffix'], theorem_name='Goal', contract_version=replay.ladder.VERSION)))
        (self.output/'sany.log').write_text('')
        (self.output/'result.json').write_text(json.dumps(record))
        return task, fragment, record

    def test_contract_raw_binding_and_tamper_detection(self):
        task, fragment, record = self.make_record()
        self.assertFalse(replay.audit_record(task, fragment, record, {'files': {}})['certified'])
        (self.output/'sany.log').write_text('tampered')
        with self.assertRaisesRegex(ValueError, 'raw log'):
            replay.audit_record(task, fragment, record, {'files': {}})

    def test_certified_without_sany_and_strict_success_rejected(self):
        task, fragment, record = self.make_record()
        record.update(certified=True, status='pass')
        (self.output/'result.json').write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'Unsupported ladder certification'):
            replay.audit_record(task, fragment, record, {'files': {}})

    def test_positive_over_deadline_or_invalid_budget_rejected(self):
        task, fragment, record = self.make_record()
        record.update(certified=True, status='pass', tlaps={'raw': 'mock'},
                      timeout_seconds=30, seconds=31)
        candidate = self.output/'Example.tla'
        candidate.write_text(task['prefix']+fragment+task['suffix'])
        java = str((self.output/'fake-java').resolve())
        jar = str(Path(replay.ladder.runner.TLA2TOOLS).resolve())
        runtime = dict(files={java: 'a'*64, jar: 'b'*64})
        record.update(candidate_path=str(candidate), dependency_sha256={})
        record['sany'].update(status='pass', java_path=java, jar_path=jar,
            java_executable_sha256='a'*64, jar_sha256='b'*64,
            library_path=replay.ladder.runner.TLA_LIBRARY, returncode=0, timed_out=False,
            output='Semantic processing of module Example\n',
            command=[java, '-Djava.io.tmpdir='+str(self.output/'jtmp'),
                '-DTLA-Library='+replay.ladder.runner.TLA_LIBRARY, '-cp',
                replay.ladder.runner.CLASSPATH, 'tla2sany.SANY', candidate.name])
        (self.output/'sany.log').write_text(record['sany']['output'])
        for seconds, timeout in [(31, 30), (1, 31), (float('inf'), 30), (1, 0)]:
            record.update(seconds=seconds, timeout_seconds=timeout)
            (self.output/'result.json').write_text(json.dumps(record))
            with patch.object(replay.ladder, '_audit_tlaps'), \
                 patch.object(replay, 'classify_outcome', return_value={'classification': 'proof_success'}):
                with self.assertRaisesRegex(ValueError, 'Unsupported ladder certification'):
                    replay.audit_record(task, fragment, record, runtime)
        record.update(seconds=1, timeout_seconds=30)
        (self.output/'result.json').write_text(json.dumps(record))
        with patch.object(replay.ladder, '_audit_tlaps'), \
             patch.object(replay, 'classify_outcome', return_value={'classification': 'proof_success'}):
            self.assertTrue(replay.audit_record(task, fragment, record, runtime)['certified'])


if __name__ == '__main__':
    unittest.main()
