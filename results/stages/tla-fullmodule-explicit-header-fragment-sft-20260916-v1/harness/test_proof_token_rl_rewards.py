"""SANY-only reward bridge tests. All checker and Java calls are mocked."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import proof_token_rl_rewards as bridge


class TokenRewardCheckTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.task = dict(prefix='---- MODULE Example ----\nTHEOREM Goal == TRUE\n',
                         suffix='\n====\n', theorem_name='Goal', dependency_sha256={})

    def evidence(self, **kw):
        value = dict(execution_complete=True, cleanup_complete=True, output_complete=True,
                     timed_out=False, returncode=0, output='Semantic processing of module Example\n',
                     seconds=.01)
        value.update(kw); return value

    def run_check(self, evidence=None, execute=None, **kw):
        with patch.object(bridge, 'validate_fragment', return_value='Example'), \
             patch.object(bridge.shutil, 'which', return_value='/usr/bin/java'):
            return bridge.check(self.task, 'BY SMT', self.root/'check',
                execute=execute or (lambda *args: evidence or self.evidence()), **kw)

    def test_sany_success_is_partial_not_proof(self):
        row = self.run_check()
        self.assertEqual(row['reward'], 1); self.assertEqual(row['status'], 'pass')
        self.assertTrue(row['partial_reward']); self.assertFalse(row['proof_certified'])
        self.assertEqual(json.loads((self.root/'check/result.json').read_bytes()), row)

    def test_known_semantic_rejection_zero(self):
        row = self.run_check(self.evidence(returncode=1, output='Semantic errors:\n*** Errors: 1\n'))
        self.assertEqual(row['reward'], 0); self.assertEqual(row['status'], 'model_sany_reject')

    def test_unknown_diagnostic_is_not_zero(self):
        row = self.run_check(self.evidence(returncode=2, output='unrecognized checker result'))
        self.assertIsNone(row['reward']); self.assertEqual(row['status'], 'unmeasured_unknown')

    def test_incomplete_cleanup_cannot_reward_rc0(self):
        row = self.run_check(self.evidence(cleanup_complete=False))
        self.assertIsNone(row['reward']); self.assertEqual(row['status'], 'unmeasured_timeout')

    def test_missing_module_is_not_model_negative(self):
        row = self.run_check(self.evidence(returncode=1, output='Could not find module Imported'))
        self.assertIsNone(row['reward']); self.assertEqual(row['status'], 'unmeasured_infrastructure')

    def test_candidate_mutation_cannot_reward(self):
        def execute(command, work, timeout):
            (work/'Example.tla').write_text('changed')
            return self.evidence()
        row = self.run_check(execute=execute)
        self.assertIsNone(row['reward']); self.assertEqual(row['status'], 'unmeasured_infrastructure')

    def test_immutable_input_mutation_cannot_reward(self):
        def execute(command, work, timeout):
            (work/'input.json').write_text('{}')
            return self.evidence()
        row = self.run_check(execute=execute)
        self.assertIsNone(row['reward'])

    def test_untrusted_dependency_cannot_reward(self):
        dep = self.root/'Dep.tla'; dep.write_text('---- MODULE Dep ----\nTHEOREM Oracle == TRUE\n====\n')
        self.task['dependency_sha256'] = {str(dep): bridge.sha(dep.read_bytes())}
        row = self.run_check()
        self.assertIsNone(row['reward'])

    def test_saved_log_and_process_binding(self):
        def execute(command, work, timeout):
            return self.evidence(command=command, cwd=str(work))
        row = self.run_check(execute=execute)
        current = dict(java=str(Path('/usr/bin/java').resolve()),
                       library=bridge.runner.TLA_LIBRARY, classpath=bridge.runner.CLASSPATH)
        with patch.object(bridge, 'validate_fragment', return_value='Example'):
            self.assertTrue(bridge.audit_check(self.task, 'BY SMT', row, current))
            log = self.root/'check/sany.log'; original = log.read_bytes()
            log.write_text('changed raw diagnostic')
            with self.assertRaisesRegex(ValueError, 'Raw SANY outcome changed'):
                bridge.audit_check(self.task, 'BY SMT', row, current)
            log.write_bytes(original)
            process = self.root/'check/process.json'; process.write_text('{}')
            with self.assertRaisesRegex(ValueError, 'Raw process evidence changed'):
                bridge.audit_check(self.task, 'BY SMT', row, current)

    def test_changed_runtime_command_fails_saved_audit(self):
        def execute(command, work, timeout):
            return self.evidence(command=command, cwd=str(work))
        row = self.run_check(execute=execute)
        current = dict(java='/wrong/java', library=bridge.runner.TLA_LIBRARY,
                       classpath=bridge.runner.CLASSPATH)
        with patch.object(bridge, 'validate_fragment', return_value='Example'):
            with self.assertRaisesRegex(ValueError, 'attested runtime'):
                bridge.audit_check(self.task, 'BY SMT', row, current)

    def test_known_contract_vs_unknown_contract(self):
        for index, (reason, expected) in enumerate([
                ('fragment must begin a proof', 0), ('unexpected scaffold fault', None)]):
            with patch.object(bridge, 'validate_fragment', side_effect=ValueError(reason)):
                row = bridge.check(self.task, 'bad', self.root/f'contract-{index}',
                                   execute=lambda *args: self.fail('Contract must not execute'))
            self.assertEqual(row['reward'], expected)


class TokenRewardLedgerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name); self.output = self.root/'rewards'
        self.control_dir = self.root/'controls'; self.control_dir.mkdir()
        self.identity = {'files': {'f': 'a'*64}}
        self.tasks = {f'task-{i}': dict(id=f'task-{i}', split='train', prefix='p', suffix='s',
            theorem_name='Goal', dependency_sha256={}, reference_fragment='BY SMT') for i in range(8)}
        self.packet = dict(tasks=[dict(id=t, prompt='p') for t in self.tasks], requests=[])
        for i in range(32):
            self.packet['requests'].append(dict(sample_id=f'sample-{i}', task_id=f'task-{i//4}',
                prompt_sha256='a'*64, policy_sha256=bridge.POLICY_SHA, split='train', reward_stage='sany_partial'))
        self.encoding = dict(rendered_prompt='p', rendered_prompt_sha256='a'*64,
            input_token_ids=[1], input_token_ids_sha256='b'*64, input_tokens=1)
        self.rows = [dict(self.encoding, status='generated', finish_reason='eos', token_ids=[2],
                          raw_reply='BY SMT') for _ in range(32)]
        self.rollouts = self.root/'rollouts.jsonl'
        self.write_rollouts()
        self.write_controls()

    def write_rollouts(self):
        self.rollouts.write_text(''.join(json.dumps(r)+'\n' for r in self.rows))

    def write_controls(self):
        # Admission is mocked in reward-loop tests after the raw control audit
        # helper is installed. Dedicated fail-closed tests below do not mock it.
        controls = [dict(task_id=t, control=label, status='pass' if label=='reference' else 'model_sany_reject',
                        reward=1 if label=='reference' else 0,
                        output='' if label=='reference' else "Unknown operator: `"+bridge.UNDEFINED+"'\n*** Errors: 1\n")
                    for t in self.tasks for label in ('reference', 'undefined_fact')]
        bridge.dump(self.control_dir/'rows.json', controls)
        bridge.dump(self.control_dir/'summary.json', dict(complete=True, correct_controls=16,
            requested_controls=16, accounted_controls=16, partial_sany_only=True,
            rows_sha256=bridge.sha((self.control_dir/'rows.json').read_bytes())))
        bridge.dump(self.control_dir/'config.json', dict(requests_sha256=bridge.REQUEST_SHA, timeout=30))
        for name in ('identity_before.json', 'identity_after.json'):
            bridge.dump(self.control_dir/name, self.identity)

    def fake_check(self, *args, **kw):
        return dict(status='pass', reward=1, partial_reward=True, proof_certified=False)

    def run_rewards(self, checker=None, identities=None):
        with patch.object(bridge, 'prepare', return_value=(self.packet, self.tasks, object())), \
             patch.object(bridge, 'identity', side_effect=identities or [self.identity, self.identity]), \
             patch.object(bridge, 'validate_rollouts') as validate, \
             patch.object(bridge, 'encode_prompt', return_value=self.encoding), \
             patch.object(bridge, 'decode_reply', return_value='BY SMT'), \
             patch.object(bridge, 'extract', return_value={'fragment': 'BY SMT'}), \
             patch.object(bridge, 'audit_check', return_value=True), \
             patch.object(bridge, 'check', side_effect=checker or self.fake_check):
            result = bridge.rewards(self.root/'requests.json', self.rollouts, self.control_dir, self.output)
            validate.assert_called_once_with(self.packet, self.rows)
            return result

    def test_full32_accounted_partial_reward_receipt(self):
        result = self.run_rewards()
        self.assertEqual(result['accounted_samples'], 32); self.assertEqual(result['positives'], 32)
        packet = json.loads((self.output/'rewards.json').read_bytes())
        self.assertEqual(packet['reward_stage'], 'sany_partial'); self.assertEqual(len(packet['rows']), 32)
        receipt = json.loads((self.output/'rewards.receipt.json').read_bytes())
        self.assertEqual(receipt['rewards_sha256'], bridge.sha((self.output/'rewards.json').read_bytes()))
        self.assertEqual(receipt['rollouts_sha256'], bridge.sha(self.rollouts.read_bytes()))

    def test_unknown_reward_remains_null_and_ineligible(self):
        self.run_rewards(checker=lambda *a, **kw: dict(status='unmeasured_unknown', reward=None))
        rows = json.loads((self.output/'rewards.json').read_bytes())['rows']
        self.assertTrue(all(r['reward'] is None and not r['reward_eligible'] and
                            not r['measured_model_outcome'] for r in rows))

    def test_time_limited_or_capped_generation_never_rewarded(self):
        self.rows[0].update(status='generation_time_limit', finish_reason='time_limit')
        self.rows[1]['finish_reason'] = 'token_limit'; self.write_rollouts()
        self.run_rewards()
        rows = json.loads((self.output/'rewards.json').read_bytes())['rows']
        self.assertTrue(all(r['reward'] is None for r in rows[:2]))
        self.assertEqual(len(rows), 32)

    def test_input_token_mismatch_no_receipt(self):
        self.rows[0]['input_token_ids'] = [99]; self.write_rollouts()
        with self.assertRaisesRegex(ValueError, 'tokenization mismatch'):
            self.run_rewards()
        self.assertFalse((self.output/'rewards.receipt.json').exists())

    def test_output_decode_mismatch_no_receipt(self):
        self.rows[0]['raw_reply'] = 'BY Other'; self.write_rollouts()
        with self.assertRaisesRegex(ValueError, 'decoding mismatch'):
            self.run_rewards()
        self.assertFalse((self.output/'rewards.receipt.json').exists())

    def test_runtime_drift_no_receipt(self):
        with self.assertRaisesRegex(ValueError, 'runtime changed'):
            self.run_rewards(identities=[self.identity, {'files': {'f': 'b'*64}}])
        self.assertFalse((self.output/'rewards.receipt.json').exists())

    def test_control_rows_hash_mismatch_rejected(self):
        (self.control_dir/'rows.json').write_text('[]')
        with self.assertRaises(ValueError): self.run_rewards()
        self.assertFalse((self.output/'rewards.receipt.json').exists())

    def test_forged_control_reordering_rejected_even_with_matching_hash(self):
        path = self.control_dir/'rows.json'
        rows = json.loads(path.read_bytes()); rows.reverse(); bridge.dump(path, rows)
        summary = json.loads((self.control_dir/'summary.json').read_bytes())
        summary['rows_sha256'] = bridge.sha(path.read_bytes())
        bridge.dump(self.control_dir/'summary.json', summary)
        with self.assertRaisesRegex(ValueError, 'ordered control population'):
            self.run_rewards()

    def test_wrong_negative_diagnostic_rejected_even_with_matching_hash(self):
        path = self.control_dir/'rows.json'
        rows = json.loads(path.read_bytes()); rows[1]['output'] = '*** Errors: 1\nSome unrelated error'
        bridge.dump(path, rows)
        summary = json.loads((self.control_dir/'summary.json').read_bytes())
        summary['rows_sha256'] = bridge.sha(path.read_bytes())
        bridge.dump(self.control_dir/'summary.json', summary)
        with self.assertRaisesRegex(ValueError, 'single undefined-fact'):
            self.run_rewards()


if __name__ == '__main__':
    unittest.main()
