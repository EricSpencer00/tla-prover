---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS None

VARIABLES none
vars == <<none>>

TypeOK ==
    /\ none \in {None}

Init ==
    /\ none = None

Next ==
    /\ UNCHANGED vars

Spec ==
    /\ Init
    /\ [][Next]_vars

SetExtensionality ==
    \A X \in SUBSET Nat, Y \in SUBSET Nat : (\A z \in Nat : (z \in X) <=> (z \in Y)) => X = Y

NoSetContainsAllValues ==
    \A Z \in SUBSET Nat : \A v \in Nat : ~(v \in Z)

====