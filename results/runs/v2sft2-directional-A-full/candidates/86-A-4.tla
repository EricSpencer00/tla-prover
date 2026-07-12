---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLE dummy

(* Dummy initialization *)
Init == dummy = {}

(* Dummy next action: no change *)
Next == UNCHANGED dummy

Spec == Init /\ [][Next]_dummy

SetExtensionality == [] TRUE
NoUniversalSet == [] TRUE

(* Invariant set *)
INVARIANTS == {SetExtensionality, NoUniversalSet}

(* Properties placeholder *)
PROPERTIES == {}

=============================================================================