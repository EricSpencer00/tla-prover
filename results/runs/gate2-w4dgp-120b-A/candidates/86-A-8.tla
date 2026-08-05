---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, none

Backends == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, none}

VARIABLES backend
vars == <<backend>>

Init == backend = none

Dispatch == \E b \in Backends : backend' = b
Idle == backend' = backend

Next == Dispatch \/ Idle

Spec == Init /\ [][Next]_vars

Extensionality == \A S, T \in SUBSET UNION {UNION} : (\A x \in UNION : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet == \A x \in UNION : x \notin UNION

====