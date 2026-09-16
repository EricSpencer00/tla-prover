"""Bounded prefix-only proof-step proposals; not a proof-language parser.

Only completed earlier labels are offered. Current/enclosing unproved labels
and ASSUME/PROVE labels are deliberately omitted. Unsupported scope constructs
return no proposals rather than guessing visibility. No answer input exists.
"""
import re

from tools.proof_source_scope import named_declarations, top_level_code


def step_candidates(prefix, theorem_name, *, visible_backends=(),
                    visible_definitions=(), limit=8):
    """Return (candidates, metadata), consuming immutable prefix/context only.

The caller establishes backend visibility (normally from frozen imports).
Definition names additionally must occur before the target in this prefix.
Candidate ordering and the <=32 limit are deterministic, with no verifier use.
"""
    if not 1 <= limit <= 32:
        raise ValueError('candidate limit must be between 1 and 32')
    if any(name not in {'SMT', 'PTL'} for name in visible_backends):
        raise ValueError('only explicitly visible SMT/PTL backends supported')
    metadata = dict(status='unsupported', reason=None, visible_steps=[],
                    current_goal=None, omitted_assumption_labels=[],
                    completion_evidence='syntactic BY/OBVIOUS or completed child QED; not independently verified',
                    reference_fragment_used=False)

    def unsupported(reason):
        metadata['reason'] = reason
        return [], metadata

    code = top_level_code(prefix)
    declarations = named_declarations(prefix)
    targets = [d for d in declarations if d.name == theorem_name]
    if len(targets) != 1 or declarations[-1] != targets[0]:
        return unsupported('target must be the unique final named declaration')
    target = targets[0]
    header = re.compile(r'(?m)^[ \t]*<(?P<level>[1-9]\d*)>'
                        r'(?P<label>[A-Za-z0-9_]+)?\.?[ \t]+')
    events = list(header.finditer(code, target.body_start))
    if not events:
        return unsupported('no hierarchical proof step at insertion point')
    if len(events) > 256:
        return unsupported('proof exceeds bounded 256-step scope')
    # Reject unrecognized angle-step forms instead of silently skipping them.
    if len(re.findall(r'(?m)^[ \t]*<', code[target.body_start:])) != len(events):
        return unsupported('unrecognized proof-step header')
    frames = {}
    current = None
    for index, event in enumerate(events):
        level = int(event['level'])
        if level > 16 or (index == 0 and level != 1):
            return unsupported('unsupported initial/deep proof level')
        if current and level > current['level'] + 1:
            return unsupported('proof level jumps over a scope')
        if current and level > current['level'] and current['complete']:
            return unsupported('child proof follows already completed step')
        for old_level in list(frames):
            if old_level > level:
                del frames[old_level]
        stop = events[index + 1].start() if index + 1 < len(events) else len(code)
        body = code[event.end():stop]
        proof = re.search(r'\b(?:BY|OBVIOUS|PROOF)\b', body)
        statement_stop = event.end() + (proof.start() if proof else len(body))
        statement_code = code[event.end():statement_stop].strip()
        kind_match = re.match(r'[A-Z]+\b', statement_code)
        kind = kind_match[0] if kind_match else 'ASSERTION'
        if kind in {'SUFFICES', 'PICK', 'HIDE', 'DEFINE', 'WITNESS', 'HAVE'}:
            return unsupported('unsupported scope command: ' + kind)
        if not statement_code:
            return unsupported('empty step statement')
        if re.search(r'\b(?:OMITTED|AXIOM|THEOREM|LEMMA)\b', body):
            return unsupported('unsupported admission/declaration in proof')
        complete = bool(proof and proof[0] in {'BY', 'OBVIOUS'})
        if index == len(events) - 1 and proof:
            return unsupported('insertion point already contains a proof')
        label = '<' + str(level) + '>' + event['label'] if event['label'] else None
        current = dict(level=level, label=label, kind=kind, complete=complete,
                       statement=prefix[event.end():statement_stop].strip())
        if kind == 'ASSUME':
            metadata['omitted_assumption_labels'].append(label)
        if kind == 'QED':
            if complete and level > 1 and frames.get(level - 1):
                frames[level - 1][-1]['complete'] = True
        elif kind not in {'TAKE', 'USE'}:
            frames.setdefault(level, []).append(current)
    # Initial contract uses only same-scope siblings. Even completed facts from
    # enclosing proof levels are omitted rather than modeling inherited scope.
    visible = [step for step in frames.get(current['level'], [])
               if step is not current and step['complete'] and step['label']
               and step['kind'] not in {'ASSUME', 'QED'}]
    labels = [s['label'] for s in visible]
    if len(labels) != len(set(labels)):
        return unsupported('ambiguous duplicate visible step labels')
    metadata['visible_steps'] = [dict(label=s['label'], statement=s['statement']) for s in visible]
    if current['kind'] not in {'QED', 'TAKE', 'USE', 'ASSUME'}:
        metadata['current_goal'] = current['statement']
    elif current['kind'] == 'QED':
        if current['level'] == 1:
            start, stop = target.body_start, events[0].start()
            intro = re.search(r'\bPROOF\b', code[start:stop])
            if intro:
                stop = start + intro.start()
            metadata['current_goal'] = prefix[start:stop].strip()
        elif frames.get(current['level'] - 1):
            metadata['current_goal'] = frames[current['level'] - 1][-1]['statement']
    metadata.update(status='supported', reason=None)
    if not labels:
        return [], metadata
    declared = set(re.findall(r'(?m)^[ \t]*([A-Za-z_]\w*)\s*(?:\([^\n]*?\))?\s*==',
                              code[:target.start]))
    definitions = list(dict.fromkeys(visible_definitions))
    if any(name not in declared for name in definitions):
        raise ValueError('definition context contains a name absent before target')
    backends = [''] + [name for name in ('SMT', 'PTL') if name in visible_backends]
    groups = [labels[-8:]] + [[label] for label in reversed(labels[-4:])]
    proposed = []
    # Cover backend alternatives before optional DEF variants. This deliberately
    # preserves actual policy choice; no candidate is selected by an oracle.
    for names in groups:
        for defs in ([], definitions):
            for backend in backends:
                candidate = 'BY ' + ', '.join(([backend] if backend else []) + names)
                if defs:
                    candidate += ' DEF ' + ', '.join(defs)
                if candidate not in proposed:
                    proposed.append(candidate)
    return proposed[:limit], metadata
