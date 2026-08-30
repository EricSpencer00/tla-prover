---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, NoTimeout, NoTactic

Backends == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

\* Dispatch a proof obligation to a configured backend prover, with an
\* optional timeout and search tactic.
Dispatch(p, t) == "Dispatch(" /\ p /\ (t = NoTactic) / ("|" /\ t /\ ")")
Timeout(o)      == "Timeout(" /\ o /\ ")"

\* Temporal-logic proof rules from Lamport's TLA+ paper; they have no
\* implementation here but are names that must be reserved.
INVARIANCE == "Invariance rule"
WFPROOF    == "Weak fairness proof rule"
SFPROOF    == "Strong fairness proof rule"
STEP        == "Step simulation rule"
WELLFORMED == "Well-formedness rule"

SPECIFICATION == "Specification"
INIT          == "Init"
NEXT          == "Next"
INVARIANTS    == "Invariants"
PROPERTIES    == "Properties"

\* Pairwise set extensionality: if two sets contain exactly the same
\* elements they are the same set.
Extensionality == \A A, B \in SUBSET Nat :
    (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

\* No set contains every natural number; since Nat is infinite this holds.
NoUniversalSet == \A A \in SUBSET Nat : \E x \in Nat : x \notin A
====