"""Opt-in whole-proof contract; not a replacement for the leaf checker.

The caller must independently freeze the target, complete prefix and dependency
closure. Only balanced ordinary comments and single-definition hierarchical
DEFINE steps extend the legacy syntax. This is deliberately not a TLA+ parser.
Real positive/negative controls must be run before admitting a new source family.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import tempfile

from . import runner
from .proof_fragment_check import _code, classify_result
from .proof_fragment_check import validate_fragment as validate_legacy

CONTRACT_VERSION = 'full-proof-fragment-v1'
_IDENT = r'[A-Za-z_][A-Za-z_0-9]*'
_STEP = re.compile(r'^\s*<(\d+)>(?:[A-Za-z_0-9]+\.)?\s*([^\n]*)', re.M)
_DEFINE = re.compile(r'DEFINE\s+(' + _IDENT + r')(?:\(\s*(' + _IDENT +
                     r'(?:\s*,\s*' + _IDENT + r')*)\s*\))?\s*==')


def validate_fragment(prefix: str, fragment: str, suffix: str, theorem_name: str) -> str:
    """Validate boundaries without rewriting a single candidate byte.

    Whole proofs only: the suffix is the module terminator, not another proof
    step. DEFINE names cannot shadow module declarations or any identifier in
    the immutable target statement; repeated local names are conservative rejects.
    """
    pre, frag, post = _code(prefix), _code(fragment), _code(suffix)
    if not prefix.endswith('\n') or not suffix.startswith('\n'):
        raise ValueError('whole-proof boundaries require separate lines')
    if _code(prefix + fragment + suffix) != pre + frag + post:
        raise ValueError('lexical state crosses a proof boundary')
    if re.search(r'\(\*\s*\{', fragment):
        raise ValueError('proof pragmas are outside the full-fragment contract')
    if not re.fullmatch(r'\s*={4,}\s*', post):
        raise ValueError('whole-proof suffix must only close the module')
    # Retain the legacy immutable-target and complete-module restrictions.
    module = validate_legacy(prefix, 'OBVIOUS', suffix, theorem_name)
    target = list(re.finditer(r'\b(?:THEOREM|LEMMA)\s+' + re.escape(theorem_name) + r'\s*==', pre))[-1]
    statement = pre[target.end():]
    if re.search(r'\b(?:PROOF|BY|OBVIOUS)\b|<\d+>', statement):
        raise ValueError('full-fragment prefix already contains target proof')
    if not re.match(r'\s*(?:PROOF\b|<\d+>|BY\b|OBVIOUS\b)', frag):
        raise ValueError('fragment must begin a proof')
    head = re.sub(r'^\s*PROOF\b', '', frag, count=1).lstrip()
    if re.match(r'(?:BY|OBVIOUS)\b', head) and re.search(r'<\d+>|\bDEFINE\b', head):
        raise ValueError('hierarchical steps cannot follow a terminal leaf proof')
    if re.search(r'\b(?:OMITTED|AXIOM|THEOREM|LEMMA|COROLLARY|PROPOSITION|MODULE|EXTENDS|INSTANCE|CONSTANTS?|VARIABLES?|RECURSIVE|LOCAL)\b|----|====', frag):
        raise ValueError('admission, declaration, or module injection')

    forbidden_names = set(re.findall(_IDENT, statement))
    forbidden_names.update(re.findall(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(' + _IDENT + r')', pre))
    forbidden_names.update(re.findall(r'^\s*(' + _IDENT + r')\s*(?:\([^\n]*?\))?\s*==', pre, re.M))
    for declaration in re.finditer(r'\b(?:CONSTANTS?|VARIABLES?)\s+([^\n]+)', pre):
        forbidden_names.update(re.findall(_IDENT, declaration.group(1)))
    forbidden_names.update(('TRUE', 'FALSE', 'BOOLEAN', 'STRING', 'Nat', 'Int', 'Real',
                            'SMT', 'PTL', 'Zenon', 'Isabelle', 'SimpleArithmetic'))
    steps = list(_STEP.finditer(frag))
    equals = set(m.start() for m in re.finditer('==', frag))
    defines = set(m.start() for m in re.finditer(r'\bDEFINE\b', frag))
    local_names: set[str] = set()
    previous_level, closed_root = 0, False
    for index, step in enumerate(steps):
        level = int(step.group(1))
        if not 1 <= level <= 32 or level > previous_level + 1 or closed_root:
            raise ValueError('unsupported hierarchical step structure')
        previous_level = level
        body = step.group(2)
        if re.match(r'QED\b', body) and level == 1:
            closed_root = True
        if not re.match(r'DEFINE\b', body):
            continue
        definition = _DEFINE.match(body)
        if not definition:
            raise ValueError('unsupported step-local DEFINE syntax')
        name, parameters = definition.groups()
        params = [p.strip() for p in parameters.split(',')] if parameters else []
        if name in forbidden_names or name in local_names or name in params or len(set(params)) != len(params):
            raise ValueError('step-local DEFINE shadows an existing name')
        local_names.add(name)
        defines.discard(step.start(2))
        equal_at = step.start(2) + definition.end() - 2
        equals.discard(equal_at)
        end = steps[index + 1].start() if index + 1 < len(steps) else len(frag)
        rhs = frag[equal_at + 2:end]
        if not rhs.strip() or re.search(r'\b(?:BY|OBVIOUS|QED|PROOF|DEFINE|LET|IN)\b', rhs):
            raise ValueError('unsupported DEFINE body or proof boundary')
    if equals or defines:
        raise ValueError('every definition must be a single explicit hierarchical DEFINE step')
    return module


def certify_fragment(prefix: str, fragment: str, suffix: str, *, theorem_name: str,
                     work_root: Path, dependencies: tuple[Path, ...] = (),
                     timeout: int = 60, tlapm: Path | None = None) -> dict:
    """Certify exact raw text with strict uncached TLAPS and full obligations."""
    work_root = Path(work_root).resolve()
    work_root.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='proof-full-', dir=work_root))
    candidate = prefix + fragment + suffix
    result = dict(contract_version=CONTRACT_VERSION, certified=False,
                  status='contract_reject', proved=0, total=0, output='',
                  seconds=0.0, workdir=str(work), reason='',
                  sha256=hashlib.sha256(candidate.encode()).hexdigest())
    (work / 'input.json').write_text(json.dumps(dict(prefix=prefix, fragment=fragment,
        suffix=suffix, theorem_name=theorem_name, contract_version=CONTRACT_VERSION)))
    try:
        name = validate_fragment(prefix, fragment, suffix, theorem_name)
        path = work / (name + '.tla')
        path.write_bytes(candidate.encode())
        result['candidate_path'] = str(path)
        seen, hashes = {path.name}, {}
        for dep in dependencies:
            dep = Path(dep)
            if dep.suffix != '.tla' or dep.name in seen:
                raise ValueError('duplicate or non-TLA dependency')
            seen.add(dep.name)
            data = dep.read_bytes()
            if re.search(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION|AXIOM)\b', _code(data.decode())):
                raise ValueError('custom dependency exports unverified theorem or axiom declarations')
            (work / dep.name).write_bytes(data)
            hashes[dep.name] = hashlib.sha256(data).hexdigest()
        result['dependency_sha256'] = hashes
        cmd = [str(tlapm or runner.TLAPM), '--strict', '--nofp', '--cache-dir', str(work / '.tlacache')]
        for directory in runner.TLA_LIBRARY.split(':'):
            cmd += ['-I', directory]
        cmd.append(path.name)
        result['command'] = cmd
        rc, output, seconds, timed_out = runner.run_cmd(cmd, work, timeout)
        status, proved, total = classify_result(rc, output, timed_out)
        result.update(status=status, proved=proved, total=total, output=output,
                      seconds=seconds, returncode=rc, timed_out=timed_out,
                      certified=status == 'pass')
    except ValueError as exc:
        result['reason'] = str(exc)
    except OSError as exc:
        result.update(status='infrastructure_error', reason=str(exc))
    (work / 'tlapm.log').write_text(result['output'])
    (work / 'result.json').write_text(json.dumps(result, indent=2))
    return result
