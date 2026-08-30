---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES val

vars == <<val>>

Init == val = One

HalfStep == val' = Half(val)

NormStep == val' = Norm(val)

Next == HalfStep \/ NormStep

TypeOK ==
    /\ One \in [num : (Nat \cup {0}), den : (Nat \cup {0})]
    /\ Half \in [ [num : (Nat \cup {0}), den : (Nat \cup {0})] -> [num : (Nat \cup {0}), den : (Nat \cup {0})] ]
    /\ Norm \in [ [num : (Nat \cup {0}), den : (Nat \cup {0})] -> [num : (Nat \cup {0}), den : (Nat \cup {0})] ]
    /\ val \in [num : (Nat \cup {0}), den : (Nat \cup {0})]

Spec == Init /\ [][Next]_vars

OnlyIntegers == val.den # 0

====