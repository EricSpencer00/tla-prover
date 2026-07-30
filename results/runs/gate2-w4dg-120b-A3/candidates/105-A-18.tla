---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm, Specification, Init, Next, Invariant, Property

CONSTANTS
    One == [num |-> 1, den |-> 1]
    Half == [num |-> 1, den |-> 2]
    Norm(x) ==
        IF x.num % 2 = 0 /\ x.den % 2 = 0
        THEN Norm([num |-> x.num \div 2, den |-> x.den \div 2])
        ELSE x

VARIABLES q
vars == << q >>

Specification == q # [num |-> 0, den |-> 1]

Init == q = One
Next == q' = Norm([num |-> q.num, den |-> q.den * 2])
Invariant == Specification
Property == TRUE

Spec == Init /\ [][Next]_vars
====