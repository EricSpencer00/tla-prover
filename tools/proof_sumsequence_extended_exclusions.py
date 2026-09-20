"""Audit the complete checked Lemma2a/Lemma3 assemblies; never admit training."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_sumsequence_exclusions as prior
from tools import proof_sumsequence_lemma2a as lemma2a


def candidates():
    from tools import proof_sumsequence_lemma3 as lemma3
    second = lemma2a.task()
    second['reference_fragment'] = 'OBVIOUS\n'
    third = lemma3.task()
    return [second, third]


def compare_candidates(tasks, sources, goals):
    checks = {}
    def compare(label, text, pool, kind):
        result = prior.breadth.compare(text, pool)
        checks[label] = dict(result, queried_sha256=prior.breadth.sha(text.encode()),
                            protected_pool=kind, overlap_exclusion=prior.overlap(result))
    for task in tasks:
        name = task['theorem_name']
        assembly = task['prefix'] + task['reference_fragment'] + task['suffix']
        compare(name + ':assembly', assembly, sources, 'sources')
        compare(name + ':reference_fragment', task['reference_fragment'], sources, 'sources')
        bodies = prior.breadth.goal_bodies(task['statement'])
        if len(bodies) != 1 or bodies[0][0] != name:
            raise ValueError('Exact target goal required')
        compare(name + ':target', bodies[0][1], goals, 'goals')
        context_goals = prior.breadth.goal_bodies(task['prefix'])
        expected = {'Lemma2a'} if name == 'Lemma2a' else {'FrontDef', 'Lemma2a', 'Lemma3'}
        if {n for n, _ in context_goals} != expected or len(context_goals) != len(expected):
            raise ValueError('Complete explicit prerequisite inventory required')
        for prerequisite, body in context_goals:
            compare(name + ':context_goal:' + prerequisite, body, goals, 'goals')
        compare(name + ':complete_context', task['prefix'], sources, 'sources')
    return checks


def audit(output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    code = (*prior.CODE, 'tools/proof_sumsequence_extended_exclusions.py',
            'tools/proof_sumsequence_lemma2a.py', 'tools/proof_sumsequence_lemma3.py')
    before = {p:prior.breadth.sha((ROOT/p).read_bytes()) for p in code}
    tasks = candidates()
    if [t['theorem_name'] for t in tasks] != ['Lemma2a', 'Lemma3']:
        raise ValueError('Exact two-target inventory required')
    sources, goals, paths, provenance = prior.population()
    checks = compare_candidates(tasks, sources, goals)
    for name, text in (
        ('original_source', prior.discovery.SOURCE.read_text()),
        ('Front_source', prior.discovery.FRONT_SOURCE.read_text()),
        ('Front_definition', prior.discovery.FRONT)):
        result = prior.breadth.compare(text, sources)
        checks[name] = dict(result, queried_sha256=prior.breadth.sha(text.encode()),
                            protected_pool='sources', overlap_exclusion=prior.overlap(result))
    paths.update({str(prior.discovery.SOURCE):prior.discovery.SOURCE_SHA,
                  str(prior.discovery.FRONT_SOURCE):prior.discovery.FRONT_SHA})
    for path, expected in paths.items():
        prior.checked(path, expected)
    after = {p:prior.breadth.sha((ROOT/p).read_bytes()) for p in code}
    if before != after:
        raise ValueError('Audit source drift')
    report = dict(schema=1, tasks=[t['theorem_name'] for t in tasks],
        task_sha256=prior.breadth.sha(json.dumps(tasks, sort_keys=True).encode()),
        threshold=prior.THRESHOLD, source_entries=len(sources), goal_entries=len(goals),
        official_sources=149, development_tasks=4, fresh_evaluation_tasks=14,
        original18_and_references=True, sources_before=before, sources_after=after,
        input_sha256=paths, protected_provenance=provenance, checks=checks,
        overlap_keys=[k for k,v in checks.items() if v['overlap_exclusion']],
        lexical_exclusion_clear=not any(v['overlap_exclusion'] for v in checks.values()),
        training_authorized=False,
        scope='Lexical source/goal exclusion only; controls and training admission remain separate')
    prior.discovery.write(output/'report.json', report)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    audit(parser.parse_args().output)
