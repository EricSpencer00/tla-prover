---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS None

VARIABLES oracle

vars == << oracle >>

Init == oracle = None

Check == oracle # None /\ oracle' = None

Dispatch ==
  \/ (oracle = None /\ oracle' = "Zenon")
  \/ (oracle = None /\ oracle' = "Isabelle")
  \/ (oracle = None /\ oracle' = "CVC3")
  \/ (oracle = None /\ oracle' = "Yices")
  \/ (oracle = None /\ oracle' = "veriT")
  \/ (oracle = None /\ oracle' = "Z3")
  \/ (oracle = None /\ oracle' = "SPASS")
  \/ (oracle = None /\ oracle' = "LS4")

Next == Dispatch \/ Check

SpecInv == Spec == Init /\ [][Next]_vars

SpecWF == Spec /\ WF_vars(Dispatch) /\ WF_vars(Check)

Extensionality ==
  \A A, B \in SUBSET Nat :
    (\A x \in Nat : x \in A <=> x \in B) => A = B

EverySetMissesSomething ==
  \A A \in SUBSET Nat : \E x \in Nat : x \notin A

Spec == SpecInv
Init == Init
Next == Next
INVARIANTS == Extensionality
PROPERTIES == EverySetMissesSomething

====