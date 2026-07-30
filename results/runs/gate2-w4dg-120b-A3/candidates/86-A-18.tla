---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS NONE, True, False, Auto, Z3, LY, L3, Y3, VT, SP, Z3SMT, Zenon, Isabelle, LS4

VARIABLES x
vars == << x >>

TypeOK == TRUE

Init == x = 0

Next == x' = (x + 1) % 2

Spec == Init /\ [][Next]_vars

Invariance(f, k) == (f) ~> (f)
WeakFAIR(f, k) == WF_vars(f)
StrongFAIR(f, k) == SF_vars(f)
WellFormed(g) == TRUE

Extensionality(ax, ay) == \A e \in ax : e \in ay => ax = ay
NoSetContainsAllValues(ax) == \A e \in ax : FALSE

Properties == Extensionality("A", "B") /\ NoSetContainsAllValues("A")
====