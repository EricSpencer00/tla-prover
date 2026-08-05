---- MODULE DyadicRationals ----
EXTENDS Integers

One == [num |-> 1, den |-> 1]

Half(f) == [num |-> f.num, den |-> f.den * 2]

RECURSIVE Norm(_)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

VARIABLES f

vars == {f}

Init == f = One

Next == \E f' \in {Half(f), Norm(f)} : f' = f'

Spec == Init /\ [][Next]_vars

====