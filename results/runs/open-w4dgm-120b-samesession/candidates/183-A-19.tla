---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS MaxDepth, TimeOut, Tactic, Debug, Mode, Repeat

\* Backend provers/SMT solvers that TLAPS may dispatch to.
Provers == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

\* Specification: the set of axioms and rules TLAPS may invoke during a proof.
Specification == {"invariance", "wellformedness", "strongfairness", "weakfairness", "simulation"}

\* Initial state: no backend task has been dispatched.
Init == TRUE

\* Next: the set of actions. Backends and proof rules are configuration, not steps.
Next == Init

\* Invariant: set extensionality (if two sets have the same members they are equal).
Extensionality == \A X \in SUBSET {1, 2, 3} : \A Y \in SUBSET {1, 2, 3} :
  (X \subseteq Y /\ Y \subseteq X) => (X = Y)

\* Property: no set can contain every element of the universe.
NoUniversalSet == \A X \in SUBSET {1, 2, 3} : X # {1, 2, 3}

StateSpace == Init

vars == << >>

Spec == Init /\ [][Next]_vars

TypeOK == TRUE

====