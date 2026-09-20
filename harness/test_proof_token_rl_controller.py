"""Mocked controller transport only: no SSH, SCP, jobs, or checker invocation."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from tools import proof_token_rl_controller as c


class ControllerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name); self.output = self.root/'output'
        self.requests = self.root/'requests.json'; self.requests.write_bytes(b'fixed requests')
        self.request_sha = c.sha(self.requests.read_bytes())
        self.raw = b'{}\n'*32
        self.ready = dict(rows=32, requests_sha256=self.request_sha,
                          policy_sha256=c.POLICY_SHA, rollouts_sha256=c.sha(self.raw))
        self.calls = []; self.remote_files = {}; self.now = 0.; self.ready_after = 0
        self.ready_polls = 0; self.state = 'R'; self.bridge_calls = 0

    def result(self, args, code=0, out='', err=''):
        return subprocess.CompletedProcess(args, code, out, err)

    def transport(self, args, **kw):
        self.calls.append(args)
        self.assertLessEqual(kw['timeout'], 30)
        self.assertTrue(kw['capture_output']); self.assertTrue(kw['text']); self.assertFalse(kw['check'])
        self.assertIn('-oBatchMode=yes', args)
        if args[0] == 'scp':
            source, dest = args[-2:]
            if source.startswith('polaris:'):
                Path(dest).write_bytes(self.raw)
            else:
                self.remote_files[dest.split(':', 1)[1]] = Path(source).read_bytes()
            return self.result(args)
        cmd = args[-1]
        if cmd.startswith('qstat'):
            return self.result(args, out='Job Id: 123.polaris\n    job_state = '+self.state+'\n')
        if cmd.startswith('if test'):
            self.ready_polls += 1
            return self.result(args, 44) if self.ready_polls <= self.ready_after else self.result(args, out=json.dumps(self.ready))
        if cmd.startswith('sha256sum '):
            path = cmd.split()[1]
            return self.result(args, out=c.sha(self.remote_files[path])+'  '+path+'\n')
        if cmd.startswith('test ! -e '):
            source, dest = cmd.split()[-2:]
            self.remote_files[dest] = self.remote_files.pop(source)
            return self.result(args)
        self.fail('Unexpected transport: '+repr(args))

    def bridge(self, requests, rollouts, controls, output):
        self.bridge_calls += 1; output.mkdir()
        reward = dict(complete=True, reward_stage='sany_partial', rows=[{}]*32,
            policy_sha256=c.POLICY_SHA, requests_sha256=self.request_sha, rollouts_sha256=c.sha(self.raw))
        c.dump(output/'rewards.json', reward)
        c.dump(output/'rewards.receipt.json', dict(provenance_verified=True,
            requests_sha256=self.request_sha, rollouts_sha256=c.sha(self.raw),
            rewards_sha256=c.sha((output/'rewards.json').read_bytes())))

    def sleep(self, seconds):
        self.assertLessEqual(seconds, 10); self.now += seconds

    def run_fake(self, **kw):
        with patch.object(c, 'REQUEST_SHA', self.request_sha):
            return c.run(kw.pop('remote_root', c.REMOTE_ROOT), '123.polaris', self.requests, self.root/'controls', self.output,
                execute=kw.pop('execute', self.transport), bridge=kw.pop('bridge', self.bridge),
                clock=lambda: self.now, sleep=kw.pop('sleep', self.sleep))

    def test_delivery_atomic_receipt_last(self):
        result = self.run_fake()
        self.assertEqual(result['status'], 'delivered'); self.assertFalse(result['job_completion_verified'])
        self.assertEqual(self.bridge_calls, 1)
        commits = [a[-1] for a in self.calls if a[0]=='ssh' and a[-1].startswith('test ! -e')]
        self.assertEqual(len(commits), 2)
        self.assertTrue(commits[0].endswith('/rewards.json'))
        self.assertTrue(commits[1].endswith('/rewards.receipt.json'))
        self.assertEqual(self.remote_files[c.REMOTE+'/rewards.json'],
                         (self.output/'reward_bridge/rewards.json').read_bytes())
        self.assertFalse(any('qsub' in str(a) for a in self.calls))

    def test_not_ready_polls_then_delivers(self):
        self.ready_after = 2
        self.run_fake(); self.assertEqual(self.ready_polls, 3); self.assertEqual(self.now, 20)

    def test_retry_routes_all_artifacts_to_new_root(self):
        root = c.REMOTE_ROOT.removesuffix('v1')+'v2'
        self.assertEqual(self.run_fake(remote_root=root)['status'], 'delivered')
        self.assertTrue(self.remote_files)
        self.assertTrue(all(path.startswith(root+'/results/cycle/training/')
                            for path in self.remote_files))
        self.assertFalse(any(c.REMOTE_ROOT in str(args) for args in self.calls))

    def test_partial_readiness_rejected(self):
        self.ready['rows'] = 31
        with self.assertRaisesRegex(ValueError, 'full32'): self.run_fake()
        self.assertEqual(self.bridge_calls, 0)

    def test_rollout_sha_mismatch_rejected(self):
        self.ready['rollouts_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'bytes/count'): self.run_fake()
        self.assertEqual(self.bridge_calls, 0)

    def test_terminal_still_inspects_ready_but_never_delivers(self):
        self.state = 'F'
        with self.assertRaisesRegex(RuntimeError, 'terminal'): self.run_fake()
        self.assertEqual(self.ready_polls, 1); self.assertEqual(self.bridge_calls, 0)
        self.assertTrue((self.output/'rollouts_ready.json').exists())

    def test_unknown_job_distinct_from_connection_failure(self):
        self.assertEqual(c.job_state(self.result([], 153, err='qstat: Unknown Job Id 123')), 'missing')
        with self.assertRaisesRegex(RuntimeError, 'transport/query'):
            c.job_state(self.result([], 255, err='Connection refused'))
        with self.assertRaisesRegex(RuntimeError, 'transport/query'):
            c.job_state(self.result([], 255, err='Unknown Job Id (untrusted SSH output)'))

    def test_connection_failure_records_failure(self):
        with self.assertRaisesRegex(RuntimeError, 'transport/query'):
            self.run_fake(execute=lambda args, **kw: self.result(args, 255, err='Connection refused'))
        self.assertTrue((self.output/'failure.json').exists()); self.assertEqual(self.bridge_calls, 0)

    def test_command_timeout_records_failure(self):
        def expired(args, **kw): raise subprocess.TimeoutExpired(args, kw['timeout'])
        with self.assertRaisesRegex(TimeoutError, 'Transport'): self.run_fake(execute=expired)
        self.assertTrue((self.output/'failure.json').exists())

    def test_total_deadline_stops_wait(self):
        self.ready_after = 10000
        def elapsed(seconds): self.now = c.SECONDS
        with self.assertRaisesRegex(TimeoutError, 'deadline'): self.run_fake(sleep=elapsed)
        self.assertEqual(self.bridge_calls, 0)

    def test_receipt_binding_tamper_never_uploaded(self):
        def wrong(*args):
            self.bridge(*args)
            path = args[-1]/'rewards.receipt.json'
            data = json.loads(path.read_bytes()); data['rewards_sha256'] = '0'*64; c.dump(path, data)
        with self.assertRaisesRegex(ValueError, 'binding mismatch'): self.run_fake(bridge=wrong)
        self.assertFalse(self.remote_files)

    def test_remote_hash_tamper_never_committed(self):
        def tamper(args, **kw):
            if args[-1].startswith('sha256sum '): return self.result(args, out='0'*64+' file\n')
            return self.transport(args, **kw)
        with self.assertRaisesRegex(ValueError, 'temporary delivery SHA'): self.run_fake(execute=tamper)
        self.assertNotIn(c.REMOTE+'/rewards.receipt.json', self.remote_files)
        self.assertNotIn(c.REMOTE+'/rewards.json', self.remote_files)

    def test_terminal_after_bridge_no_receipt(self):
        def terminal(*args): self.bridge(*args); self.state = 'F'
        with self.assertRaisesRegex(RuntimeError, 'terminal'): self.run_fake(bridge=terminal)
        self.assertNotIn(c.REMOTE+'/rewards.receipt.json', self.remote_files)

    def test_shell_payload_targets_rejected_without_transport(self):
        for root, job in [(c.REMOTE_ROOT+';echo bad', '123'), (c.REMOTE_ROOT, '123;echo bad'),
                          (c.REMOTE_ROOT, '$(evil)'), (c.REMOTE_ROOT, '-123')]:
            with self.assertRaises(ValueError): c.validate_target(root, job)
        c.validate_target(c.REMOTE_ROOT, '123')
        self.assertEqual(self.calls, [])


if __name__ == '__main__':
    unittest.main()
