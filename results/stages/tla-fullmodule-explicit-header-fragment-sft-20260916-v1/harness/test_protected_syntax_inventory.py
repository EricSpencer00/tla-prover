from tools.protected_syntax_inventory import complete, inventory, leaves


def node(kind, image='', *children):
    return dict(kind=kind, image=image, children=list(children))


def test_empty_structural_prefix_is_not_an_operator_token():
    op = node('N_GenInfixOp', '', node('N_IdPrefix', 'N_IdPrefix'),
              node('N_InfixOp', '='))
    assert leaves(op) == '='
    counts, operators = inventory(node('N_InfixExpr', '', node('token', 'x'), op,
                                       node('N_Number', '', node('token', '0'))))
    assert counts['N_InfixExpr'] == 1
    assert operators == {'=': 1}


def test_truncated_or_unreaped_process_is_not_complete():
    assert not complete({'execution_complete': True, 'output_complete': True})
    assert complete(dict(execution_complete=True, cleanup_complete=True, output_complete=True))
