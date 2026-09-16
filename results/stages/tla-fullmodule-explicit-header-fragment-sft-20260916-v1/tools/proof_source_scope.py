"""Conservative lexical source scope for retrieval, not a TLA+ parser.

Offsets are Python string offsets. Imports, INSTANCE substitutions, proof-step
scope and declaration bodies are deliberately not interpreted here.
"""
from dataclasses import dataclass
import re


def _blank(text):
    return ''.join(c if c in '\r\n' else ' ' for c in text)


def top_level_code(source):
    """Mask comments, strings, nested modules and the outer module trailer.

Retain length and newline positions, including CRLF. An unfinished module
prefix and headerless fixture text are accepted. The first module header is
the outer header only when no substantive code precedes it; otherwise it is
a nested module. A missing nested-module terminator hides the remaining text.
Trailing material after the outer terminator is never lexed.
"""
    output = []
    comment_depth = nested = 0
    outer_header = substantive = closed = False
    for line in source.splitlines(keepends=True):
        if closed:
            output.append(_blank(line))
            continue
        masked, i = [], 0
        while i < len(line):
            if line.startswith('(*', i):
                comment_depth += 1
                masked.append('  ')
                i += 2
            elif comment_depth and line.startswith('*)', i):
                comment_depth -= 1
                masked.append('  ')
                i += 2
            elif comment_depth:
                masked.append(_blank(line[i]))
                i += 1
            elif line.startswith('\\*', i):
                masked.append(_blank(line[i:]))
                break
            elif line.startswith('*)', i):
                raise ValueError('unmatched comment terminator')
            elif line[i] == '"':
                start = i
                i += 1
                while i < len(line) and line[i] not in '"\r\n':
                    i += 2 if line[i] == '\\' else 1
                if i >= len(line) or line[i] != '"':
                    raise ValueError('unterminated string')
                i += 1
                masked.append(_blank(line[start:i]))
            else:
                masked.append(line[i])
                i += 1
        code = ''.join(masked)
        header = re.match(r'^\s*-{4,}\s*MODULE\s+\w+\s*-{4,}\s*$', code)
        ending = re.match(r'^\s*={4,}\s*$', code)
        if header:
            if not outer_header and not substantive and not nested:
                outer_header = True
            else:
                nested += 1
            output.append(_blank(line))
        elif ending:
            if nested:
                nested -= 1
            else:
                closed = True
            output.append(_blank(line))
        elif nested:
            output.append(_blank(line))
        else:
            substantive = substantive or bool(code.strip())
            output.append(code)
    if comment_depth and not closed:
        raise ValueError('unclosed comment')
    return ''.join(output)


@dataclass(frozen=True)
class NamedDeclaration:
    name: str
    kind: str
    start: int
    body_start: int
    local: bool


def named_declarations(source, *, exported=False):
    """Index named fact headers, optionally excluding LOCAL imported facts.

LOCAL belongs to the declaration even across newlines/comments. Current-module
retrieval may use these local facts; importing modules may not. The returned
body_start does not determine the end of a statement or certify visibility
inside proof scopes. Consumers still delimit bodies and exclude target/later
declarations. Operator definitions and INSTANCE exports are not indexed.
"""
    code = top_level_code(source)
    pattern = re.compile(
        r'(?m)^[ \t]*(?P<local>LOCAL\s+)?'
        r'(?P<kind>THEOREM|LEMMA|AXIOM|ASSUME)\s+'
        r'(?P<name>\w+)\s*==')
    result = []
    for match in pattern.finditer(code):
        local = match['local'] is not None
        if not (exported and local):
            result.append(NamedDeclaration(match['name'], match['kind'],
                                           match.start(), match.end(), local))
    return result
