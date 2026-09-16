"""Detect TLA+ comment markers in a repair continuation.

Comments are legal TLA+, but they consume the bounded repair budget without
adding model semantics.  This narrow repair-time guard is admitted only for
the two protected references, which are independently comment-free; it is not
a universal TLA+ grammar or acceptance claim.
"""


def comment_guard(text):
    hits = []
    for line_number, line in enumerate(text.splitlines(), 1):
        quoted = False
        index = 0
        while index + 1 < len(line):
            char = line[index]
            if char == '"' and (index == 0 or line[index - 1] != "\\"):
                quoted = not quoted
                index += 1
                continue
            if not quoted and line.startswith("\\*", index):
                hits.append({"line": line_number, "column": index + 1,
                             "kind": "comment_marker"})
                break
            index += 1
    return hits

