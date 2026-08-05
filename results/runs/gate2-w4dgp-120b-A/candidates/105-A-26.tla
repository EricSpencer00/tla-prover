---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES t
vars == <<t>>

Init ==
    t = [num |-> 1, den |-> 1]

OneDef ==
    One = [num |-> 1, den |-> 1]

HalfDef ==
    Half = [num |-> t.num, den |-> t.den * 2]

NormDef ==
    Norm = IF t.num % 2 = 0 /\ t.den % 2 = 0
           THEN [num |-> t.num \div 2, den |-> t.den \div 2]
           ELSE t

Next ==
    \/ OneDef
    \/ HalfDef
    \/ NormDef

Spec == Init /\ [][Next]_vars /\ \A p \in {One, Half, Norm} : TRUE

====