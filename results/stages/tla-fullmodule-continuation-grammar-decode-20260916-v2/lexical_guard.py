"""Reject the observed invalid adjacent relational operator corruption.

This is a narrow decoder guard, not a replacement for SANY. TLA+ permits
hash and less-than as separate operators, but the observed model repair
emitted the adjacent byte sequence #<, which SANY rejects. Strings are
ignored so the guard does not reinterpret string contents.
"""


def lexical_guard(text):
    hits = []
    for line_number, line in enumerate(text.splitlines(), 1):
        quoted = False
        index = 0
        while index < len(line):
            char = line[index]
            if char == '"' and (index == 0 or line[index - 1] != chr(92)):
                quoted = not quoted
                index += 1
                continue
            if not quoted:
                for marker in ("#<", "#>"):
                    if line.startswith(marker, index):
                        hits.append({
                            "line": line_number,
                            "column": index + 1,
                            "kind": "invalid_adjacent_relational_operator",
                            "marker": marker,
                        })
                        break
            index += 1
    return hits
