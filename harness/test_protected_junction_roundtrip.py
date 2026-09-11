import pytest

from tools.protected_junction_roundtrip import canonical, junction, normalize


def node(kind, image='', *children):
    return dict(kind=kind, image=image, children=list(children))


def test_operator_leaf_images_are_never_discarded():
    assert canonical(node('N_InfixOp', '=')) != canonical(node('N_InfixOp', '#'))
    assert canonical(node('N_PrefixOp', '~')) != canonical(node('N_PrefixOp', '[]'))
    assert canonical(node('token', 'p')) != canonical(node('token', 'q'))


def test_parentheses_and_associative_lists_normalize_without_reordering():
    p, q, r = [node('token', name) for name in ('p', 'q', 'r')]
    paren = node('N_ParenExpr', '', node('token', '('), p, node('token', ')'))
    assert canonical(paren) == canonical(p)
    listed = node('N_ConjList', '',
                  node('N_ConjItem', '', node('token', '/\\'), p),
                  node('N_ConjItem', '', node('token', '/\\'), q))
    infix = node('N_InfixExpr', '', p, node('N_InfixOp', '/\\'), q)
    assert canonical(listed) == canonical(infix)
    cp, cq, cr = map(canonical, (p, q, r))
    assert junction('/\\', [junction('/\\', [cp, cq]), cr]) == junction('/\\', [cp, cq, cr])
    assert junction('/\\', [cp, cq]) != junction('/\\', [cq, cp])
    assert junction('/\\', [cp, cq]) != junction('\\/', [cp, cq])


@pytest.mark.parametrize('text', ['\tF == TRUE', 'F == TRUE\r\n', 'F == "é"'])
def test_unsupported_columns_are_explicit(text):
    with pytest.raises(ValueError):
        normalize(text, {})


def test_junction_edits_keep_comment_gap_bytes():
    text = '---- MODULE C ----\nF == /\\ TRUE \\* keep this\n     /\\ FALSE\n====\n'

    def located(kind, image, start, end, *children):
        return dict(node(kind, image, *children), start=start, end=end)

    first = located('N_ConjItem', '', [2, 6], [2, 12],
                    located('token', '/\\', [2, 6], [2, 7]),
                    located('token', 'TRUE', [2, 9], [2, 12]))
    second = located('N_ConjItem', '', [3, 6], [3, 13],
                     located('token', '/\\', [3, 6], [3, 7]),
                     located('token', 'FALSE', [3, 9], [3, 13]))
    tree = located('N_Module', '', [1, 1], [4, 4],
                   located('N_ConjList', '', [2, 6], [3, 13], first, second))
    normalized = normalize(text, tree)
    assert ' \\* keep this\n     ' in normalized
    assert normalized.count('\\* keep this') == 1
    assert '(TRUE)' in normalized and '(FALSE)' in normalized
    assert normalized.startswith('---- MODULE C ----\nF == ')
    assert normalized.endswith('\n====\n')
