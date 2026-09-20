import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch, MagicMock

from tools import proof_cuda_repair_eval as probe


class Tokenizer:
    def apply_chat_template(self,messages,**kwargs):
        return '<BOS>'+messages[0]['content']+'<ASSISTANT>'
    def __call__(self,text,**kwargs):
        assert kwargs==dict(add_special_tokens=False,truncation=False)
        return dict(input_ids=[1,2,3])


def fixture():
    tasks=[dict(id=str(i),split='train' if i<17 else 'development',prompt='p',prompt_sha256=probe.sha(b'p')) for i in range(21)]
    packet=dict(schema=1,manifest_sha256=probe.MANIFEST_SHA256,tasks=tasks,requested_tasks=21,
                reference_fragments_exported=False,candidates_exported=False)
    raw=json.dumps(packet).encode()
    files={'config.json':'abc'}
    config=dict(**probe.BUDGET,prompts_sha256=probe.sha(raw),model_files=files,
                model_files_sha256=probe.digest(files),requested_task_ids=[t['id'] for t in tasks],
                restore_exact=True,arm='base',checkpoint_sha256=None,
                implementation_sha256={n:'a'*64 for n in probe.IMPLEMENTATION})
    row=probe.encode_prompt(Tokenizer(),tasks[0])
    row.update(status='generated',token_ids=[4],token_ids_sha256=probe.digest([4]),output_tokens=1,
               hit_token_limit=False,raw_reply='BY SMT',raw_reply_sha256=probe.sha(b'BY SMT'))
    summary=dict(termination='phase_timeout',unattempted_task_ids=[t['id'] for t in tasks[1:]])
    return raw,config,[row],summary


class RepairProbeTests(unittest.TestCase):
    def test_partial_keeps_full_denominator(self):
        self.assertEqual(len(probe.validate_run(*fixture())),21)

    def test_no_double_bos_encoder(self):
        row=probe.encode_prompt(Tokenizer(),dict(id='x',split='train',prompt='p',prompt_sha256='h'))
        self.assertEqual(row['input_token_ids'],[1,2,3])

    def test_budget_is_1024_not_shared_512(self):
        tokenizer=Tokenizer()
        tokenizer.__class__=type('LongTokenizer',(Tokenizer,),{'__call__':lambda self,*a,**kw:dict(input_ids=[1]*7300)})
        row=probe.encode_prompt(tokenizer,dict(id='x',split='train',prompt='p',prompt_sha256='h'))
        self.assertEqual(row['status'],'context_overflow')

    def test_reject_reference_export(self):
        packet=json.loads(fixture()[0]);packet['tasks'][0]['reference_fragment']='BY SMT'
        with self.assertRaises(ValueError):probe.validate_export(packet)

    def test_reject_population_change(self):
        packet=json.loads(fixture()[0]);packet['tasks'][0]['split']='development'
        with self.assertRaises(ValueError):probe.validate_export(packet)

    def test_reject_manifest_change(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'m.json';path.write_text('{}')
            with self.assertRaisesRegex(ValueError,'exact frozen'):probe.export_tasks(path)

    def test_reject_run_tampering(self):
        mutations=[lambda c,r,s:c.update(max_new_tokens=512),
                   lambda c,r,s:c.update(restore_exact=False),
                   lambda c,r,s:c.update(checkpoint_sha256='x'),
                   lambda c,r,s:r[0].update(raw_reply='changed'),
                   lambda c,r,s:r[0].update(token_ids=[4,5]),
                   lambda c,r,s:r[0].update(split='development'),
                   lambda c,r,s:r[0].update(status='context_overflow'),
                   lambda c,r,s:s.update(termination='complete'),
                   lambda c,r,s:s.update(unattempted_task_ids=[])]
        for mutation in mutations:
            raw,c,r,s=fixture();mutation(c,r,s)
            with self.assertRaises(ValueError):probe.validate_run(raw,c,r,s)

    def test_reject_duplicate_rows(self):
        raw,c,r,s=fixture();r.append(copy.deepcopy(r[0]))
        with self.assertRaises(ValueError):probe.validate_run(raw,c,r,s)

    def test_supervisor_kills_and_reaps_timed_out_group(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);prompts=root/'prompts.json';prompts.write_bytes(fixture()[0])
            out=root/'out';out.mkdir()
            a=type('Args',(),dict(prompts=prompts,output=out,model_path=root/'model',checkpoint=None))()
            process=MagicMock(pid=987,returncode=-9);process.poll.return_value=None
            with patch('tools.proof_cuda_train.model_files',return_value={'config.json':'h'}), \
                 patch.object(probe.subprocess,'Popen',return_value=process), \
                 patch.object(probe.time,'monotonic',side_effect=[0,601,602]), \
                 patch.object(probe.os,'killpg') as kill:
                probe.generate(a)
            kill.assert_called_once_with(987,probe.signal.SIGKILL)
            process.wait.assert_called_once()
            summary=json.loads((out/'summary.json').read_bytes())
            self.assertEqual(summary['termination'],'phase_timeout')
            self.assertEqual(len(summary['unattempted_task_ids']),21)

    def test_shared_reconstruction_rejects_input_and_output_changes(self):
        from tools.proof_cuda_eval import validate_tokenization
        tokenizer=Tokenizer()
        tokenizer.decode=lambda *args,**kwargs:'BY SMT'
        tokenizer.clean_up_tokenization_spaces=False
        raw,_,rows,_=fixture();task=json.loads(raw)['tasks'][0]
        validate_tokenization(tokenizer,task,rows[0])
        rows[0]['input_token_ids']=[1,1,2,3]
        with self.assertRaises(ValueError):validate_tokenization(tokenizer,task,rows[0])
        rows[0]['input_token_ids']=[1,2,3];rows[0]['raw_reply']='BY FALSE'
        with self.assertRaises(ValueError):validate_tokenization(tokenizer,task,rows[0])

    def test_actual_frozen_packet_contains_no_answers(self):
        path=probe.ROOT/'results/runs/proof-multistep-manifest-20260905-v2/manifest.json'
        packet,tasks=probe.export_tasks(path)
        self.assertEqual(len(tasks),21)
        self.assertTrue(all(set(t)=={'id','split','prompt','prompt_sha256'} for t in packet['tasks']))

    def test_local_verify_preserves_exact_hole(self):
        raw,config,rows,summary=fixture()
        tasks=[dict(id=str(i),split='train' if i<17 else 'development',prefix='PREFIX\n',suffix='\nSUFFIX',
                    theorem_name='Goal',dependencies=[]) for i in range(21)]
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);out=root/'out';out.mkdir();gen=root/'gen';gen.mkdir();tok=root/'tok';tok.mkdir()
            (tok/'config.json').write_text('{}')
            config['model_files']={'config.json':probe.sha(b'{}')};config['model_files_sha256']=probe.digest(config['model_files'])
            prompts=root/'prompts.json';prompts.write_bytes(raw)
            for n,d in [('config',config),('summary',summary)]:probe.dump(gen/(n+'.json'),d)
            (gen/'generations.jsonl').write_text(json.dumps(rows[0])+'\n')
            a=type('Args',(),dict(prompts=prompts,manifest=root/'m',generations=gen,tokenizer_path=tok,output=out))()
            with patch.object(probe,'export_tasks',return_value=(json.loads(raw),tasks)), \
                 patch('transformers.AutoTokenizer.from_pretrained',return_value=Tokenizer()), \
                 patch('tools.proof_cuda_eval.validate_tokenization'), \
                 patch('harness.proof_gen.extract_proof_block',return_value='BY SMT'), \
                 patch('harness.proof_fragment_check.certify_fragment',return_value=dict(certified=True,status='pass',returncode=0)) as certify:
                probe.verify(a)
            self.assertEqual(certify.call_args.args,('PREFIX\n','BY SMT','\nSUFFIX'))
            self.assertEqual(certify.call_args.kwargs['timeout'],30)
            result=json.loads((out/'summary.json').read_bytes())
            self.assertEqual(result['per_split']['train']['requested_tasks'],17)
            self.assertEqual(result['per_split']['development']['requested_tasks'],4)


if __name__=='__main__':unittest.main()
