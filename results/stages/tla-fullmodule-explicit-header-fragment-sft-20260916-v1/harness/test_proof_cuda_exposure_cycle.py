import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from tools import proof_cuda_exposure_cycle as cycle


class ExposureCycleTests(unittest.TestCase):
    def fixture(self,root):
        prior=root/'prior';prior.mkdir();(prior/'training').mkdir()
        train=root/'train.json';prompts=root/'prompts.json'
        train.write_text(json.dumps(dict(packet_kind='frozen32_broader_whole_target_proofs',evidence={'control':'bound'})))
        prompts.write_text('{}')
        rows=[dict(id=str(i),prompt='p'+str(i)) for i in range(32)]
        tasks=[dict(r,split='train') for r in rows]+[dict(id='d'+str(i),prompt='d',split='development') for i in range(4)]
        frozen=dict(train_input_sha256='train',prompts_sha256='prompts',train_ids=[r['id'] for r in rows],
                    implementation_sha256={'tools/original.py':'source'})
        (prior/'config.json').write_text(json.dumps(dict(frozen=frozen)))
        (prior/'summary.json').write_text(json.dumps(dict(status='developmental_generation_cycle_complete',
            train_retention_tasks=32,reused_development_tasks=4)))
        return prior,train,prompts,rows,tasks

    def freeze_fixture(self,root,mutate=None,sha_mutation=None):
        prior,train,prompts,rows,tasks=self.fixture(root)
        if mutate:mutate(prior,train,prompts,rows,tasks)
        def file_sha(path):
            result='train' if path==train else 'prompts' if path==prompts else cycle.PARENT_SHA if path.name=='policy_optimizer.pt' else 'source'
            return sha_mutation(path,result) if sha_mutation else result
        trainer=SimpleNamespace(SOURCES=('tools/new_trainer.py',))
        admission=dict(model_files={'model':'hash'},eos_token_ids=[1])
        transformers=SimpleNamespace(AutoTokenizer=SimpleNamespace(from_pretrained=lambda *a,**k:object()))
        with patch.dict('sys.modules',{'tools.proof_cuda_exposure_train':trainer,'transformers':transformers}), \
             patch('tools.proof_cuda_exposure_train',trainer,create=True), \
             patch.object(cycle,'file_sha',side_effect=file_sha), \
             patch.object(cycle,'validate_packet',return_value=rows), \
             patch.object(cycle,'validate_export',return_value=tasks), \
             patch.object(cycle,'check_training') as trained, \
             patch.object(cycle,'check_probe') as probe, \
             patch.object(cycle,'check_encodings') as encodings, \
             patch.object(cycle.probe,'admit',return_value=admission) as admit, \
             patch.object(cycle,'artifact_hashes',return_value={'completed':'hash'}):
            result=cycle.freeze(train,prompts,cycle.MODEL_PATH,prior,'train','prompts')
            self.assertEqual(trained.call_count,1);self.assertEqual(probe.call_count,2)
            self.assertEqual(encodings.call_count,1);self.assertEqual(admit.call_count,2)
            self.assertEqual(probe.call_args_list[0].args[3],None)
            self.assertEqual(probe.call_args_list[1].args[3],cycle.PARENT_SHA)
            return result

    def test_full_preflight_reuses_complete_bound_probes(self):
        with tempfile.TemporaryDirectory() as d:result=self.freeze_fixture(Path(d))
        self.assertEqual(result['parent_checkpoint_sha256'],cycle.PARENT_SHA)
        self.assertEqual(result['prior_artifacts_sha256'],{'completed':'hash'})
        self.assertIn('tools/proof_cuda_exposure_cycle.py',result['implementation_sha256'])
        self.assertIn('tools/new_trainer.py',result['implementation_sha256'])

    def test_changed_packet_parent_or_original_runtime_rejected(self):
        for target in ('train.json','prompts.json','policy_optimizer.pt','original.py'):
            with self.subTest(target=target),tempfile.TemporaryDirectory() as d,self.assertRaises(ValueError):
                self.freeze_fixture(Path(d),sha_mutation=lambda p,h:'changed' if p.name==target else h)

    def test_incomplete_failed_prior_rejected(self):
        for mode in ('failure','incomplete','population'):
            def mutate(prior,*args):
                if mode=='failure':(prior/'failure.json').write_text('{}')
                else:
                    p=prior/'summary.json';s=json.loads(p.read_text())
                    s['status' if mode=='incomplete' else 'train_retention_tasks']='bad';p.write_text(json.dumps(s))
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as d,self.assertRaises(ValueError):
                self.freeze_fixture(Path(d),mutate=mutate)

    def test_wrong_training_population_or_prompts_rejected(self):
        for mode in ('count','prompt','kind'):
            def mutate(prior,train,prompts,rows,tasks):
                if mode=='count':rows.pop()
                elif mode=='prompt':tasks[0]['prompt']='changed'
                else:
                    s=json.loads(train.read_text());s['packet_kind']='other';train.write_text(json.dumps(s))
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as d,self.assertRaises(ValueError):
                self.freeze_fixture(Path(d),mutate=mutate)

    def test_prior_input_drift_rejected(self):
        def mutate(prior,*args):
            p=prior/'config.json';s=json.loads(p.read_text());s['frozen']['train_input_sha256']='changed';p.write_text(json.dumps(s))
        with tempfile.TemporaryDirectory() as d,self.assertRaises(ValueError):self.freeze_fixture(Path(d),mutate=mutate)

    def execute_fixture(self,root,fail=None):
        root.mkdir(exist_ok=True);prompts=root/'prompts.json';prompts.write_text('{}')
        events=[]
        def run(commands,logs,seconds):
            phase='train' if len(events)==0 else 'probe';events.append((phase,commands,seconds))
            if fail==phase:raise RuntimeError('phase failure')
        def guard():
            events.append(('guard',))
            if fail=='guard':raise ValueError('identity drift')
        def validate(*args):
            events.append(('validate',))
            if fail=='validation':raise ValueError('incomplete training')
            return dict(checkpoint_sha256='new512')
        trainer=SimpleNamespace(validate_training=validate)
        frozen=dict(train_input_sha256='train',prompts_sha256='prompts',prior_artifacts_sha256={})
        with patch.dict('sys.modules',{'tools.proof_cuda_exposure_train':trainer}), \
             patch('tools.proof_cuda_exposure_train',trainer,create=True), \
             patch.object(cycle,'run_processes',side_effect=run), \
             patch.object(cycle,'check_probe',return_value={'generated':36}):
            result=cycle.execute(root,root/'train.json',prompts,root/'model',root/'prior',frozen,guard,object())
        return result,events

    def test_phase_order_and_budgets(self):
        with tempfile.TemporaryDirectory() as d:result,events=self.execute_fixture(Path(d))
        self.assertEqual([e[0] for e in events],['train','guard','validate','probe','guard'])
        self.assertEqual(events[0][2],620);self.assertEqual(events[3][2],1220)
        self.assertIn('512',events[0][1][0])
        self.assertEqual([r['phase'] for r in result],['reused_complete100step_probes','fresh512step_sft','child_probe'])

    def test_failures_never_advance_to_child(self):
        for mode in ('train','guard','validation'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory() as d:
                root=Path(d)
                with self.assertRaises((ValueError,RuntimeError)):self.execute_fixture(root,mode)
                rows=json.loads((root/'progress.json').read_text())
                self.assertEqual(len(rows),1)

    def test_prior_artifacts_are_content_hashed(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);(p/'a').write_text('a');first=cycle.artifact_hashes(p)
            (p/'a').write_text('b');self.assertNotEqual(first,cycle.artifact_hashes(p))


if __name__=='__main__':unittest.main()
