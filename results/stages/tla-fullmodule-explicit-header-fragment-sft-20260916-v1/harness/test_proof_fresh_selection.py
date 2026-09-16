import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import proof_fresh_selection as selection


class FreshSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Actual local immutable artifacts; no checker, sampling or training.
        cls.selected=selection.construct()

    def test_exact14_evaluation_only_population(self):
        s=self.selected
        self.assertEqual(s['requested_evaluation'],14)
        self.assertEqual(s['requested_train'],0)
        self.assertFalse(s['training_authorized']);self.assertFalse(s['evaluation_authorized'])
        self.assertEqual([t['id'] for t in s['tasks']],selection.EVAL_IDS)
        self.assertEqual({t['split'] for t in s['tasks']},{'fresh_evaluation'})
        self.assertTrue(all(not t['rejection_reasons'] for t in s['tasks']))
        self.assertEqual(len({t['source_family'] for t in s['tasks']}),6)
        self.assertEqual(s['control_budget'],dict(seconds=1000,timeout=30,requested_controls=28))

    def test_exact_exclusion_accounting(self):
        self.assertEqual(self.selected['exclusion_counts'],dict(source_entries=316,goal_entries=901,
            distinct_train_ids=99,training_rows_with_historical_repeats=105,train_raw_paths=17))
        provenance=self.selected['exclusion_sha256']
        self.assertIn('original18_reference_audit',provenance)
        self.assertIn(str(selection.ROOT/'results/runs/proof-candidate-rl-20260905-v1/frozen.json'),provenance)
        self.assertIn(str(selection.ROOT/'results/runs/proof-cuda-cycle-20260905-v2/training/train.json'),provenance)

    def test_scoped_false_retains_reference_and_assumptions(self):
        original=copy.deepcopy(self.selected)
        for task in self.selected['tasks']:
            mutated=selection.wrong_conclusion(task)
            self.assertIn('FALSE',mutated)
            if 'ASSUME' in task['target_goal']:
                self.assertIn('ASSUME',mutated[task['goal_offsets'][0]:])
        self.assertEqual(original,self.selected)

    def test_exact_reference_assembly_and_source_git(self):
        for row,(relative,name,begin,proof,end) in zip(self.selected['tasks'],selection.SELECTION):
            path,text=selection.source(relative)
            lines=text.splitlines(keepends=True)
            self.assertEqual(row['reference_fragment'],''.join(lines[proof-1:end]))
            self.assertEqual(row['prefix'],''.join(lines[:proof-1]))
            self.assertEqual(selection.sha((row['prefix']+row['reference_fragment']+row['suffix']).encode()),row['assembled_sha256'])
            self.assertEqual(selection.file_sha(path),selection.HASHES[relative])

    def test_hash_and_git_mismatch_fail_closed(self):
        relative=selection.SELECTION[0][0]
        with patch.dict(selection.HASHES,{relative:'0'*64}):
            with self.assertRaises(ValueError):selection.source(relative)
        with patch.object(selection.subprocess,'check_output',return_value=b'changed Git blob'):
            with self.assertRaises(ValueError):selection.source(relative)
        with self.assertRaises(ValueError):selection.source('unfrozen/Source.tla')

    def test_training_packet_or_config_identity_change_rejected(self):
        changed=list(selection.CUDA_INPUTS)
        run,key,config,packet=changed[0];changed[0]=(run,key,config,'0'*64)
        with patch.object(selection,'CUDA_INPUTS',tuple(changed)):
            with self.assertRaises(ValueError):selection.training_inputs()

    def test_actual_training_inputs_have_pinned_provenance(self):
        manifests,rl,provenance=selection.training_inputs()
        self.assertEqual(len(provenance),20)
        self.assertEqual(len(rl),17)
        self.assertEqual(set(manifests),{'earlier6','leaf50','hier17','whole6','new26'})

    def test_reference_free_prompts_match_exact_measured_counts(self):
        packet=selection.export_prompts(self.selected)
        self.assertFalse(packet['reference_fragments_exported'])
        self.assertFalse(packet['training_authorized'])
        self.assertEqual([r['input_tokens'] for r in packet['token_feasibility']['rows']],selection.EXPECTED_PROMPT_COUNTS)
        for row in packet['tasks']:
            self.assertEqual(set(row),{'id','split','prompt','prompt_sha256'})
            self.assertEqual(row['split'],'fresh_evaluation')
            self.assertEqual(selection.sha(row['prompt'].encode()),row['prompt_sha256'])
        self.assertTrue(all(n+3072<=8192 for n in selection.EXPECTED_PROMPT_COUNTS))

    def test_tokenizer_identity_change_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            for name in selection.TOKENIZER_HASHES:(root/name).write_bytes(b'changed')
            with self.assertRaises(ValueError):selection.export_prompts(self.selected,root)

    def test_identity_binds_selection_and_all_code_without_checker(self):
        with patch.object(selection,'construct',return_value=self.selected), \
             patch.object(selection,'runtime_identity',return_value={'mock_runtime':'unchanged'}):
            result=selection.identity(self.selected)
        self.assertEqual(result['fresh_selection_sha256'],selection.selection_digest(self.selected))
        for name in selection.IMPLEMENTATION:self.assertIn(str(selection.ROOT/name),result['fresh_inputs_sha256'])
        changed=copy.deepcopy(self.selected);changed['requested_evaluation']=13
        with patch.object(selection,'construct',return_value=self.selected):
            with self.assertRaises(ValueError):selection.identity(changed)

    def test_overlap_is_rejected_without_shrinking(self):
        # Avoid recomputing actual exclusions; only synthetic overlap comparison.
        fake=([],[],{},self.selected['exclusion_counts'])
        with patch.object(selection,'exclusions',return_value=fake), \
             patch.object(selection.legacy,'compare',return_value=dict(max_jaccard=1.0,nearest='excluded',exact_normalized=['excluded'])):
            s=selection.construct()
        self.assertEqual(len(s['tasks']),14)
        self.assertTrue(all(t['rejection_reasons'] for t in s['tasks']))
        self.assertFalse(s['evaluation_authorized'])


if __name__=='__main__':unittest.main()
