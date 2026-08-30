---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Operators == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

SPECIFICATION ==
    \A a \in Operators : TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == TRUE

PROPERTIES ==
    /\ \A S, T \in SUBSET Nat : (\A x \in S : x \in T) /\ (\A x \in T : x \in S) => S = T
    /\ \A S \in SUBSET Nat : \E x \in Nat : x \notin S

====