---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
    NoBackend, Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Backends == {NoBackend, Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

VARIABLES prov, timeout, tactic

vars == <<prov, timeout, tactic>>

TypeOK ==
    /\ prov \in Backends
    /\ timeout \in Nat
    /\ tactic \in BOOLEAN

Init ==
    /\ prov = NoBackend
    /\ timeout = 0
    /\ tactic = FALSE

SetExtensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) = (x \in B)) => A = B

NoSetContainsAll == \A B \in SUBSET Nat : (\A x \in Nat : x \in B) => (B # Nat)

INVARIANTS == {SetExtensionality, NoSetContainsAll}

InitState == UNCHANGED vars

SpecDone == UNCHANGED vars

SPECIFICATION == Init \/ SpecDone

PROPERTIES == {SpecDone}

====