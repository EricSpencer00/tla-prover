import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from tools import proof_broader_symbolic as search


def fixture():
    return [dict(id=name,prefix='---- MODULE Test ----\nTHEOREM Target == TRUE\n',
        suffix='\n====\n',theorem_name='Target',dependencies=[],dependency_sha256={},
        source_path=__file__,source_sha256=search.file_sha(__file__),library_sha256={},
        candidates=['OBVIOUS','BY DEF Foo'],candidate_sha256=[search.sha(c.encode()) for c in ('OBVIOUS','BY DEF Foo')])
        for name in search.TRAIN_IDS]


def positive(p,f,s,**kwargs):
    return dict(certified=True,returncode=0,total=2,proved=2,status='pass',timed_out=False,
        contract_version='full-proof-fragment-v1',command=['tlapm','--strict','--nofp'],
        sha256=search.sha((p+f+s).encode()),dependency_sha256={})


class SymbolicTests(unittest.TestCase):
    def run_fake(self,tasks=None,checker=None,**kwargs):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            result=search.evaluate(tasks or fixture(),root,checker=checker or (lambda *a,**k:dict(certified=False,status='failed')),
                identity=kwargs.pop('identity',lambda:{'runtime':'frozen'}),source_check=kwargs.pop('source_check',lambda t:{'source':'frozen'}),**kwargs)
            return result,json.loads((root/'outcomes.json').read_bytes())

    def test_round_robin_before_second_slot_and_first_pass_stop(self):
        calls=[]
        def checker(p,f,s,**kw):
            calls.append((kw['work_root'].parent.name,f,kw['timeout']))
            result=positive(p,f,s);result['certified']=f=='BY DEF Foo';return result
        result,rows=self.run_fake(checker=checker)
        self.assertEqual([c[0] for c in calls[:32]],search.TRAIN_IDS)
        self.assertEqual(len(calls),64);self.assertTrue(all(c[2]==5 for c in calls))
        self.assertEqual(result['certified_tasks'],32)
        self.assertEqual(result['per_population']['original6']['requested_tasks'],6)
        self.assertEqual(result['per_population']['new26']['requested_tasks'],26)

    def test_first_pass_skips_later_attempt(self):
        result,_=self.run_fake(checker=positive)
        self.assertEqual(result['checker_attempts'],32)

    def test_timeout_retains_all_unattempted(self):
        times=iter([0,0,596,597,598,599])
        result,rows=self.run_fake(clock=lambda:next(times))
        self.assertEqual(result['termination'],'time_budget')
        self.assertEqual(result['requested_tasks'],32)
        self.assertEqual(result['attempted_tasks'],0)
        self.assertEqual(len(rows),32)

    def test_false_certifications_rejected(self):
        for mutation in ({'total':0,'proved':0},{'returncode':10},{'proved':1,'total':2}):
            with self.subTest(mutation=mutation):
                outcome=dict(certified=True,returncode=0,total=1,proved=1,status='pass');outcome.update(mutation)
                result,_=self.run_fake(checker=lambda *a,**k:outcome)
                self.assertEqual(result['certified_tasks'],0)

    def test_verifier_drift_invalidates_every_positive(self):
        versions=iter([{'version':1},{'version':2}])
        result,rows=self.run_fake(identity=lambda:next(versions),checker=positive)
        self.assertFalse(result['identity_stable']);self.assertEqual(result['certified_tasks'],0)
        self.assertTrue(all(r['status']=='invalidated' for r in rows))

    def test_source_drift_raises_and_saves_full_invalidated_denominator(self):
        calls=0
        def identity(tasks):
            nonlocal calls
            calls+=1
            return {'hash':str(calls)}
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)
            with self.assertRaises(ValueError):search.evaluate(fixture(),path,identity=lambda:{},source_check=identity)
            self.assertEqual(len(json.loads((path/'outcomes.json').read_bytes())),32)
            self.assertFalse(json.loads((path/'summary.json').read_bytes())['identity_stable'])

    def test_wrong_population_and_candidate_hash_rejected(self):
        for mode in ('population','hash','budget'):
            tasks=fixture()
            if mode=='population':tasks.pop()
            if mode=='hash':tasks[0]['candidate_sha256'][0]='bad'
            if mode=='budget':tasks[0]['candidates']*=5
            with self.subTest(mode=mode),self.assertRaises(ValueError):self.run_fake(tasks=tasks)

    def test_positive_admission_requires_exact_contract_command_and_bytes(self):
        task=fixture()[0];fragment='OBVIOUS'
        baseline=positive(task['prefix'],fragment,task['suffix'])
        self.assertTrue(search.admitted(task,fragment,baseline))
        for mutation in ({'command':['tlapm','--nofp']},{'command':['tlapm','--strict']},
            {'timed_out':True},{'contract_version':'legacy'},{'sha256':'bad'},
            {'dependency_sha256':{'Injected.tla':'bad'}},{'proved':0},{'status':'unknown'}):
            with self.subTest(mutation=mutation):
                result=dict(baseline,**mutation)
                self.assertFalse(search.admitted(task,fragment,result))

    def test_whole_target_no_step_fallback_and_backend_filter(self):
        task=fixture()[0]
        result=search.candidates_for(task,[])
        self.assertEqual(result['candidates'],['OBVIOUS'])
        self.assertEqual(result['step_context']['status'],'unsupported')
        self.assertIn('no hierarchical proof',result['step_context']['reason'])
        self.assertFalse(result['reference_fragment_used'])

    def test_reference_field_is_not_used_by_candidate_builder(self):
        task=fixture()[0];before=search.candidates_for(task,[])
        task['reference_fragment']='UNIQUE SECRET ORACLE PROOF'
        self.assertEqual(before,search.candidates_for(task,[]))
        self.assertNotIn('UNIQUE',json.dumps(before))

    def test_target_proof_prefix_and_instance_fail_closed(self):
        for suffix in ('BY SMT\n',''):
            task=fixture()[0]
            if suffix:task['prefix']+=suffix
            else:task['prefix']=task['prefix'].replace('THEOREM','X == INSTANCE Hidden\nTHEOREM')
            with self.assertRaises(ValueError):search.candidates_for(task,[])

    def test_dependency_trust_and_hash_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            dep=Path(directory)/'Custom.tla';dep.write_text('---- MODULE Custom ----\nTHEOREM Cheat == TRUE\nOMITTED\n====\n')
            task=fixture()[0];task.update(dependencies=[str(dep)],dependency_sha256={str(dep):search.file_sha(dep)})
            with self.assertRaises(ValueError):search.visible_context(task,[directory])
            task['dependency_sha256'][str(dep)]='bad'
            with self.assertRaises(ValueError):search.visible_context(task,[directory])

    def test_explicit_import_resolution_excludes_unimported_library(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            (root/'Used.tla').write_text('---- MODULE Used ----\nTHEOREM Fact == TRUE\nOBVIOUS\n====\n')
            (root/'Unused.tla').write_text('---- MODULE Unused ----\nTHEOREM Secret == TRUE\nOBVIOUS\n====\n')
            task=fixture()[0];task['prefix']=task['prefix'].replace('THEOREM','EXTENDS Used\nTHEOREM')
            _,libraries,hashes=search.visible_context(task,[root])
            self.assertEqual(set(hashes),{str(root/'Used.tla')})
            self.assertNotIn('Secret',''.join(libraries))


if __name__=='__main__':unittest.main()
