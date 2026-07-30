---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : (Nat \ {0}) \cup {0}, den : (Nat \ {0}) \cup {0}]
    /\ One \in [num : (Nat \ {0}) \cup {0}, den : (Nat \ {0}) \cup {0}]
    /\ Half \in [num : (Nat \ {0}) \cup {0}, den : (Nat \ {0}) \cup {0}]
    /\ Norm \in [num : (Nat \ {0}) \cup {0}, den : (Nat \ {0}) \cup {0} -> [num : (Nat \ {0}) \cup {0}, den : (Nat \ {0}) \cup {0}]]

SpecOne == [num |-> 1, den |-> 1]

SpecHalf == [num |-> 1, den |-> 2]

SpecNorm ==
    [num |-> IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN p.num \div 2
              ELSE p.num,
     den |-> IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN p.den \div 2
              ELSE p.den]

Init ==
    /\ p = SpecOne
    /\ One = SpecOne
    /\ Half = SpecHalf
    /\ Norm = SpecNorm

Next ==
    \/ /\ p' = [num |-> p.num, den |-> p.den * 2]
    \/ /\ p' = [num |-> p.num \div 2, den |-> p.den \div 2]
    \/ /\ p' = [num |-> p.num, den |-> p.den]
    /\ UNCHANGED <<One, Half, Norm>>

Spec == Init /\ [][Next]_vars

Specification ==
    /\ Spec = SpecOne
    /\ Half = SpecHalf
    /\ Norm = SpecNorm
    /\ IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm = [num |-> p.num \div 2, den |-> p.den \div 2] ELSE Norm = [num |-> p.num, den |-> p.den]

InitInv == Spec

NextInv == Spec

SpecProp == Spec
====