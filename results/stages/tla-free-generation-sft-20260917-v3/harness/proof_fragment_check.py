"""Fail-closed TLAPS checking for a trusted, immutable proof-hole skeleton.

This deliberately restricted curriculum helper is not a general TLA+ parser or
semantic audit. Callers must freeze/review prefix and suffix and dependencies;
the hole must lie in the final theorem's proof, never its statement. No legacy
benchmark scoring or population membership is changed here.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import tempfile

from . import runner


def _code(text: str, *, reject_comments: bool = False) -> str:
    """Mask strings/comments, respecting nested TLA block comments."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('(*', i):
            if reject_comments:
                raise ValueError('comments are outside the fragment contract')
            depth += 1
            out.append('  ')
            i += 2
        elif depth and text.startswith('*)', i):
            depth -= 1
            out.append('  ')
            i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text.startswith('\\*', i):
            if reject_comments:
                raise ValueError('comments are outside the fragment contract')
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.append(' ' * (end - i))
            i = end
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == '\n':
                    raise ValueError('unterminated string')
                if text[i] == '\\':
                    out.append(' ')
                    i += 1
                if i < len(text):
                    out.append(' ')
                    i += 1
            if i == len(text):
                raise ValueError('unterminated string')
            out.append(' ')
            i += 1
        elif text.startswith('*)', i):
            raise ValueError('unmatched comment terminator')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('unclosed comment')
    return ''.join(out)


def validate_fragment(prefix: str, fragment: str, suffix: str, theorem_name: str) -> str:
    """Return the module name or reject an unsafe/unsupported hole contract."""
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', theorem_name):
        raise ValueError('invalid theorem name')
    frag = _code(fragment, reject_comments=True)
    if not frag.strip():
        raise ValueError('empty fragment')
    if re.search(r'\b(?:OMITTED|AXIOM|THEOREM|LEMMA|COROLLARY|PROPOSITION|MODULE|EXTENDS|INSTANCE|CONSTANTS?|VARIABLES?|RECURSIVE|DEFINE)\b|==|----|====', frag):
        raise ValueError('admission, declaration, or module injection')
    pre, post = _code(prefix), _code(suffix)
    assembled = _code(prefix + fragment + suffix)
    if re.search(r'\bOMITTED\b', assembled):
        raise ValueError('assembled proof contains an admission')
    # TLA+ identifiers can begin with digits provided they contain a letter.
    # Official protocol modules use names such as 2_TCommit. Keep the filename
    # alphabet restricted; this is not permission for paths or punctuation.
    module = re.match(r'\s*-{4,}\s*MODULE\s+([A-Za-z_0-9]*[A-Za-z][A-Za-z_0-9]*)\s*-{4,}', pre)
    if not module:
        raise ValueError('missing module header')
    targets = list(re.finditer(r'\b(?:THEOREM|LEMMA)\s+' + re.escape(theorem_name) + r'\s*==', pre))
    if len(targets) != 1:
        raise ValueError('target declaration must occur exactly once in prefix')
    target_tail = pre[targets[0].end():]
    if re.search(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION|MODULE)\b|====', target_tail + re.sub(r'\n={4,}\s*$', '', post)):
        raise ValueError('target must be final theorem')
    if not re.search(r'\n\s*(?:PROOF\b|<\d+>|BY\b|OBVIOUS\b)', target_tail):
        if not re.match(r'\s*(?:PROOF\b|<\d+>|BY\b|OBVIOUS\b)', frag):
            raise ValueError('hole is not demonstrably in a proof')
    if not re.fullmatch(r'[\s\S]*?\n={4,}\s*', post):
        raise ValueError('suffix must close the module')
    # A frozen skeleton containing admissions is not eligible for rewards either.
    if re.search(r'\bOMITTED\b', pre) or re.search(r'\bOMITTED\b', post):
        raise ValueError('skeleton contains an admission')
    return module.group(1)


def classify_result(rc: int, output: str, timed_out: bool) -> tuple[str, int, int]:
    if timed_out:
        return 'timeout', 0, 0
    matches = re.findall(r'^\s*(?:\[INFO\]: )?All (\d+) obligations? proved\.?\s*$', output, re.M)
    if rc != 0:
        return 'verifier_reject', 0, 0
    if re.search(r'\b(?:failed|omitted|interrupted|error|exception)\b', output, re.I):
        return 'error', 0, 0
    if len(matches) != 1:
        return 'unrecognized_output', 0, 0
    total = int(matches[0])
    return ('pass' if total > 0 else 'no_obligations'), total, total


def certify_fragment(prefix: str, fragment: str, suffix: str, *, theorem_name: str,
                     work_root: Path, dependencies: tuple[Path, ...] = (),
                     timeout: int = 60, tlapm: Path | None = None) -> dict:
    """Persist every candidate; run strict, uncached TLAPS in a unique directory.

    A verifier_reject is not automatically a model failure: callers must retain
    diagnostics and distinguish missing backends and other infrastructure errors.
    """
    work_root = Path(work_root).resolve()
    work_root.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='proof-', dir=work_root))
    candidate = prefix + fragment + suffix
    result = dict(certified=False, status='contract_reject', proved=0, total=0,
                  output='', seconds=0.0, workdir=str(work), reason='',
                  sha256=hashlib.sha256(candidate.encode()).hexdigest())
    (work / 'input.json').write_text(json.dumps(dict(prefix=prefix, fragment=fragment,
                                                   suffix=suffix, theorem_name=theorem_name)))
    try:
        name = validate_fragment(prefix, fragment, suffix, theorem_name)
        path = work / (name + '.tla')
        path.write_text(candidate)
        result['candidate_path'] = str(path)
        seen = {path.name}
        hashes = {}
        for dep in dependencies:
            dep = Path(dep)
            if dep.suffix != '.tla' or dep.name in seen:
                raise ValueError('duplicate or non-TLA dependency')
            seen.add(dep.name)
            data = dep.read_bytes()
            # Imported theorem declarations are trusted by TLAPS. Arbitrary
            # task-provided proof libraries need independent certification;
            # otherwise an unproved copy of the target can supply its own proof.
            if re.search(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION)\b', _code(data.decode())):
                raise ValueError('custom dependency exports theorem declarations without independent certification')
            (work / dep.name).write_bytes(data)
            hashes[dep.name] = hashlib.sha256(data).hexdigest()
        result['dependency_sha256'] = hashes
        legacy = os.environ.get('PROVE_TLA_TLAPM_LEGACY') == '1'
        strict_flags = [] if legacy else ['--strict']
        cache_flags = [] if legacy else ['--cache-dir', str(work / '.tlacache')]
        thread_flags = ['--threads', '1'] if legacy else []
        cmd = [str(tlapm or runner.TLAPM), *strict_flags, '--nofp', *cache_flags, *thread_flags]
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
