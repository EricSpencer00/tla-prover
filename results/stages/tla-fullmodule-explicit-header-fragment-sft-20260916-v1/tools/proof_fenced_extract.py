"""Post-hoc exact-byte proof extraction; no checker or historical output edits.

Fenced target declarations are removable wrappers only when their complete raw
statement matches the immutable task, trimming outer whitespace only. This is
not normalization, theorem repair, or a claim that the extracted proof is valid.
"""
import hashlib
import re

from harness.proof_fragment_check import _code

VERSION='exact-fenced-proof-v1'
_FENCE=re.compile(r'(?m)^[ \t]*(`{3,})([^\r\n]*)\r?$')
_START=re.compile(r'(?m)^[ \t]*(?:PROOF\b|<\d+>|BY\b|OBVIOUS\b|OMITTED\b)')
_DECL=re.compile(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION|AXIOM|MODULE|EXTENDS|INSTANCE|CONSTANTS?|VARIABLES?|RECURSIVE|LOCAL)\b')
_NAMED=re.compile(r'\A\s*(?:THEOREM|LEMMA)\s+([A-Za-z_][A-Za-z_0-9]*)\s*==')


def _sha(text):return hashlib.sha256(text.encode()).hexdigest()


def _bounds(text,start,end):
    while start<end and text[start].isspace():start+=1
    while end>start and text[end-1].isspace():end-=1
    return start,end


def _proof_safety(fragment):
    code=_code(fragment)
    first=_START.search(code)
    if first is None or code[:first.start()].strip():raise ValueError('Selected fragment does not start a proof')
    if _DECL.search(code) or '----' in code or '====' in code or '```' in code:
        raise ValueError('Declaration, module boundary or fence in selected proof')
    if re.search(r'(?m)^[ \t]*[A-Za-z_][A-Za-z_0-9]*(?:\([^\n]*\))?[ \t]*==',code):
        raise ValueError('Top-level operator declaration in selected proof')


def _target_identity(task):
    name=task['theorem_name'];prefix=task['prefix'];goal=task['target_goal']
    declarations=list(re.finditer(r'\b(?:THEOREM|LEMMA)\s+'+re.escape(name)+r'\s*==',_code(prefix)))
    if len(declarations)!=1 or prefix[declarations[0].end():].strip()!=goal.strip():
        raise ValueError('Task goal does not exactly bind its immutable prefix')


def _fenced_bounds(reply,start,end,task):
    raw=reply[start:end]
    # A complete module is accepted only with the literal immutable prefix.
    if re.match(r'\s*-{4,}\s*MODULE\b',_code(raw)):
        prefix=task['prefix']
        if not raw.startswith(prefix):raise ValueError('Fenced module prefix differs from immutable task')
        closing=re.search(r'(?m)^[ \t]*={4,}[ \t]*(?:\r?\n)?\s*\Z',_code(raw))
        if closing is None or closing.start()<len(prefix):raise ValueError('Fenced module has no isolated closing terminator')
        return (*_bounds(reply,start+len(prefix),start+closing.start()),'fenced_exact_module')
    start,end=_bounds(reply,start,end);raw=reply[start:end];code=_code(raw)
    named=_NAMED.match(code)
    if named:
        if named[1]!=task['theorem_name']:raise ValueError('Fenced declaration names a different theorem')
        if len(list(_DECL.finditer(code)))!=1:raise ValueError('Multiple or injected declarations inside fenced target')
        proof=_START.search(code,named.end())
        if proof is None:raise ValueError('Fenced target contains no proof start')
        if raw[named.end():proof.start()].strip()!=task['target_goal'].strip():
            raise ValueError('Fenced target statement differs from immutable task')
        return (*_bounds(reply,start+proof.start(),end),'fenced_exact_target')
    if _DECL.search(code):raise ValueError('Unsupported declaration wrapper in fenced block')
    first=_START.search(code)
    if first is None or code[:first.start()].strip():raise ValueError('Fenced block is not proof-only or an exact target wrapper')
    return start,end,'fenced_proof_only'


def extraction(reply,task):
    """Return raw/fragment hashes and character+UTF8-byte offsets; never rewrite.

    Any multiple/unterminated/unsupported fences fail closed. Unfenced proof-only
    replies keep the legacy first-proof-line-to-end behavior, except declarations
    before or within that span are rejected rather than silently discarded.
    """
    if not isinstance(reply,str):raise TypeError('Raw reply must be a string')
    result=dict(extractor_version=VERSION,raw_sha256=_sha(reply),fragment=None,fragment_sha256=None,
                status='extraction_reject',fragment_offsets=None,fragment_byte_offsets=None,reason='',mode=None)
    try:
        _target_identity(task)
        if not reply.strip():raise ValueError('Empty reply')
        fences=list(_FENCE.finditer(reply))
        if fences:
            if len(fences)!=2:raise ValueError('Ambiguous multiple or unterminated fenced blocks')
            opening,closing=fences
            if (opening[1]!='```' or closing[1]!='```' or opening[2].strip().lower() not in ('','tla','tlaplus','tla+') or
                    closing[2].strip()):raise ValueError('Unsupported or mismatched fence delimiters')
            outside=reply[:opening.start()]+reply[closing.end():]
            if _START.search(_code(outside)):
                raise ValueError('Ambiguous additional proof outside fenced block')
            start=opening.end()
            if start>=len(reply) or reply[start]!='\n':raise ValueError('Fence content must start on the next line')
            start+=1;end=closing.start()
            start,end,mode=_fenced_bounds(reply,start,end,task)
        else:
            if '```' in reply:raise ValueError('Malformed or inline fenced block')
            code=_code(reply)
            if _DECL.search(code):raise ValueError('Unfenced declaration wrapper or injection is unsupported')
            proof=_START.search(code)
            if proof is None:raise ValueError('No proof-shaped line')
            start,end=_bounds(reply,proof.start(),len(reply));mode='unfenced_legacy_span'
        fragment=reply[start:end]
        _proof_safety(fragment)
        result.update(fragment=fragment,fragment_sha256=_sha(fragment),status='extracted',
            fragment_offsets=[start,end],fragment_byte_offsets=[len(reply[:start].encode()),len(reply[:end].encode())],
            mode=mode,reason='Exact original substring; immutable statement preserved; proof validity unmeasured')
    except (ValueError,KeyError,TypeError) as exc:
        result['reason']=str(exc)
    return result


extract=extraction
