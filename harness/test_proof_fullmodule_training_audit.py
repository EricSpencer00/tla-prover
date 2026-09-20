import copy
from unittest.mock import patch
import pytest
from tools import proof_fullmodule_training_audit as a


def test_even_selection_full_population_not_first_wave():
    selected=a.indices()
    assert len(selected)==len(set(selected))==128 and selected[0]==0 and selected[-1]==5009
    assert set(y-x for x,y in zip(selected,selected[1:]))=={39,40}


@pytest.mark.parametrize('args',[(10,11),(10,1),(128.0,2),(5010,128.0)])
def test_bad_selection(args):
    with pytest.raises(ValueError):a.indices(*args)


@pytest.fixture(scope='module')
def candidates():return a.candidates()


def test_actual_complete_corpus_binding(candidates):
    assert a.digest(a.inventory())==a.INPUTS_SHA
    assert len(candidates)==128 and [r['index'] for r in candidates]==a.indices()
    assert candidates[0]['raw']['_shard']==0 and candidates[-1]['raw']['_shard']==200
    assert all(a.digest(r['raw'])==r['raw_sha256'] and r['matching_source_lines'] for r in candidates)


def test_corpus_drift():
    with patch.object(a.w4_corpus,'load_effective',return_value=[]):
        with pytest.raises(ValueError):a.candidates()


def test_empty_protected_pool_never_clear():
    with pytest.raises(ValueError):a.compare('TRUE',[])


def test_comparison_preserves_established_helper():
    rows=[('one','x = 1'),('two','y = 2')]
    assert a.compare('x = 1',a.pool(rows))==a.exclusion.compare('x = 1',rows)
    assert a.compare('x = 1',a.pool(rows))['exact_normalized']==['one']


def test_missing_historical_status_not_clear():
    row=dict(spec_text='---- MODULE Toy ----\nInv == x = 1\n====',nl='a system')
    sources=a.pool([('other','unrelated source material')]);goals=a.pool([('g','other goal')])
    result=a.exclusion_audit(row,sources,goals)
    assert result['status']=='unknown_invariant_goal' and not result['invariant_resolved']


def test_invariant_overlap_is_not_hidden_by_whole_module():
    row=dict(spec_text='---- MODULE Toy ----\nInv == x = 1\n====',nl='a system',property_invariant='Inv')
    result=a.exclusion_audit(row,a.pool([('s','unrelated source material')]),a.pool([('goal','x = 1')]))
    assert result['status']=='excluded_lexical_overlap'


def test_fresh_unknown_denominator_kept(candidates):
    rows=[dict(r,exclusions=None,encoded=None) for r in candidates]
    result=a.summarize(rows,False)
    assert result['selected_candidates']==result['sany_outcomes_unknown']==result['exclusion_unknown']==128
    assert result['sany_checks_performed']==0 and not result['training_ready']
    with pytest.raises(ValueError):a.summarize(rows[:-1],False)


def test_actual_llama_shape_no_cfg_target(candidates):
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(a.framing.TOKENIZER,local_files_only=True)
    for index in [0,64,127]:
        raw=candidates[index]['raw'];value=a.encode(raw,tokenizer)
        assert value['response']==raw['spec_text']
        assert value['prompt']==a.gen_eval.build_generation_prompt({'system_overview':raw['nl']},raw['cfg_text'],raw['module'],None)
        ids=value['encoding']['input_ids'];n=value['encoding']['prompt_tokens']
        assert value['encoding']['labels']==[-100]*n+ids[n:]
        assert ids[-1]==tokenizer.eos_token_id and not value['truncation']


def test_inherited_prompt_flag_rejected(monkeypatch,candidates):
    monkeypatch.setenv('TLA_PROMPT_ARITY','1')
    with pytest.raises(ValueError):a.encode(candidates[0]['raw'],None)


def test_no_checker_or_model_execution_in_audit_source():
    text=(a.ROOT/'tools/proof_fullmodule_training_audit.py').read_text()
    assert 'certify_fragment(' not in text and 'check_sany(' not in text
    assert 'AutoModelForCausalLM' not in text and 'optimizer.step(' not in text


def test_complete_local_import_sources():
    import subprocess,sys
    code="""from tools import proof_fullmodule_training_audit as a
import sys
from pathlib import Path
missing=[]
for name,module in list(sys.modules.items()):
 filename=getattr(module,'__file__',None)
 if not filename or not name.startswith(('tools.','harness.')):continue
 path=Path(filename).resolve()
 if path.is_relative_to(a.ROOT) and str(path.relative_to(a.ROOT)) not in a.SOURCES:missing.append(str(path))
assert not missing,missing
"""
    result=subprocess.run([sys.executable,'-c',code],cwd=a.ROOT,capture_output=True,text=True,timeout=30)
    assert result.returncode==0,result.stdout+result.stderr
