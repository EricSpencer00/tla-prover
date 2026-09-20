import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from tools import proof_broader_symbolic_v2 as search
from harness.test_proof_broader_symbolic import fixture,positive


def source_task():
    task=fixture()[0]
    task['prefix']='---- MODULE Test ----\nD == {1}\nUnused == 0\nTHEOREM Earlier == 1 \\in D\nOBVIOUS\nTHEOREM Target == 1 \\in D\n'
    return task


class SymbolicV2Tests(unittest.TestCase):
    def test_local_and_local_definition_slots_before_imports(self):
        task=source_task()
        result=search.candidate_pool(task,[])
        self.assertIn('BY Earlier',result['candidates'])
        self.assertIn('BY Earlier DEF D',result['candidates'])
        self.assertNotIn('Unused',result['statement_context']['goal_relevant_definitions'])
        self.assertLessEqual(len(result['candidates']),8)
        self.assertFalse(result['smt_visible'])
        self.assertFalse(any('SMT' in c for c in result['candidates']))

    def test_zero_relevance_and_invisible_facts_excluded(self):
        task=source_task()
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            (root/'Visible.tla').write_text('---- MODULE Visible ----\nTHEOREM Useful == 1 \\in D\nOBVIOUS\nTHEOREM Unrelated == TotallyDifferent\nOBVIOUS\nLOCAL THEOREM Hidden == 1 \\in D\nOBVIOUS\n====\nTHEOREM Trailer == 1 \\in D\n')
            (root/'Unimported.tla').write_text('---- MODULE Unimported ----\nTHEOREM Secret == 1 \\in D\nOBVIOUS\n====\n')
            task['prefix']=task['prefix'].replace('D ==','EXTENDS Visible\nD ==',1)
            result=search.candidate_pool(task,[root])
        pool='\n'.join(result['candidates'])
        for name in ('Hidden','Trailer','Secret','Unrelated','Target'):
            self.assertNotIn(name,pool)
        self.assertEqual(result['zero_relevance_imports_omitted'],1)
        self.assertEqual([f['name'] for f in result['statement_context']['ranked_imported_facts']],['Useful'])
        self.assertLess(result['candidates'].index('BY Earlier'),next(i for i,c in enumerate(result['candidates']) if 'Useful' in c))

    def test_oracle_field_does_not_change_candidates(self):
        task=source_task();before=search.candidate_pool(task,[])
        task.update(reference_fragment='ORACLE SECRET',target_goal='FAKE GOAL',candidates=['BY Oracle'])
        self.assertEqual(before,search.candidate_pool(task,[]))

    def test_deterministic_and_strict_full_fragment(self):
        task=source_task();a=search.candidate_pool(task,[]);b=search.candidate_pool(task,[])
        self.assertEqual(a,b)
        self.assertEqual(len(a['candidates']),len(set(a['candidates'])))
        for candidate in a['candidates']:search.validate_fragment(task['prefix'],candidate,task['suffix'],task['theorem_name'])
        self.assertEqual(a['step_context']['proposed_steps'],[])

    def test_no_nonexistent_definitions(self):
        task=source_task();task['prefix']=task['prefix'].replace('1 \\in D\n', 'Missing(D)\n')
        result=search.candidate_pool(task,[])
        self.assertEqual(result['statement_context']['goal_relevant_definitions'],['D'])

    def test_instance_remains_unsupported(self):
        task=source_task();task['prefix']=task['prefix'].replace('D ==','X == INSTANCE Other\nD ==',1)
        with self.assertRaises(ValueError):search.candidate_pool(task,[])

    def test_population_requires_same_unsupported(self):
        tasks=fixture()
        for t in tasks:t['preparation_status']='ready'
        with patch.object(search.base,'prepare',return_value=tasks):
            with self.assertRaises(ValueError):search.prepare()

    def test_interim_running_until_final_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);calls=[]
            def checker(p,f,s,**kwargs):
                interim=json.loads((root/'summary.json').read_bytes())
                self.assertEqual(interim['termination'],'running')
                self.assertFalse(interim['verification_complete'])
                calls.append(kwargs['work_root'].parent.name)
                return positive(p,f,s)
            result=search.evaluate(fixture(),root,checker=checker,identity=lambda:{},source_check=lambda tasks:{})
            self.assertEqual(calls,search.TRAIN_IDS)
            self.assertEqual(result['termination'],'complete')
            self.assertTrue(result['verification_complete'])
            self.assertEqual(result['certified_tasks'],32)

    def test_verifier_drift_cannot_publish_complete(self):
        with tempfile.TemporaryDirectory() as directory:
            versions=iter([{'v':1},{'v':2}])
            result=search.evaluate(fixture(),Path(directory),checker=positive,identity=lambda:next(versions),source_check=lambda tasks:{})
            self.assertFalse(result['verification_complete'])
            self.assertFalse(result['identity_stable'])
            self.assertEqual(result['certified_tasks'],0)

    def test_budget_and_unknown_timeout_unsupported_distinct(self):
        tasks=fixture();tasks[-1].update(candidates=[],candidate_sha256=[])
        def checker(p,f,s,**kwargs):
            if kwargs['work_root'].parent.name==tasks[0]['id']:return dict(timed_out=True,status='timeout')
            return dict(status='infrastructure_error')
        with tempfile.TemporaryDirectory() as directory:
            result=search.evaluate(tasks,Path(directory),checker=checker,identity=lambda:{},source_check=lambda tasks:{})
        self.assertEqual(result['status_counts'],dict(timeout=1,unknown=30,unsupported=1))
        self.assertTrue(result['verification_complete'])

    def test_exception_finalization_fail_closed(self):
        def checker(*args,**kwargs):raise RuntimeError('failed checker')
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            with self.assertRaises(RuntimeError):search.evaluate(fixture(),root,checker=checker,identity=lambda:{},source_check=lambda tasks:{})
            result=json.loads((root/'summary.json').read_bytes())
            self.assertFalse(result['verification_complete']);self.assertEqual(result['certified_tasks'],0)

    def test_snapshot_covers_frozen_original_and_new_code(self):
        self.assertIn('tools/proof_broader_symbolic.py',search.IMPLEMENTATION)
        self.assertIn('tools/proof_broader_symbolic_v2.py',search.IMPLEMENTATION)
        self.assertEqual(search.file_sha(search.ROOT/'tools/proof_broader_symbolic.py'),search.BASE_SHA)


if __name__=='__main__':unittest.main()
