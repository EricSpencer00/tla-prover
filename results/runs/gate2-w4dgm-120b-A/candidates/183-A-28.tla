---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Spec == Zenon /\ Isabelle /\ CVC3 /\ Yices /\ VeriT /\ Z3 /\ SPASS /\ LS4

Invariance(a) == a
WellFormed(a) == a
StrongFair(a) == a
WeakFair(a) == a
StepSim(a, b) == a = b

SetExtensionality == \A A, B \in SUBSET {1, 2, 3} : (\A x \in {1, 2, 3} : (x \in A) <=> (x \in B)) => (A = B)
NoSetContainsAll == \A A \in SUBSET {1, 2, 3} : (1 \in A /\ 2 \in A /\ 3 \in A) => (A = {})

INVARIANTS == SetExtensionality
PROPERTIES == NoSetContainsAll
====