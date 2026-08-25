---- MODULE TLAPS ----
EXTENDS TLC

(* Backend pragma operators for TLAPS *)
Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
VeriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

VARIABLE dummy

INIT == dummy = FALSE

NEXT == dummy' = ~dummy

SPECIFICATION == INIT /\ [][NEXT]_<<dummy>>

INVARIANTS == {}

PROPERTIES == {}

THEOREM SetExtensionality == ∀ A, B : (∀ x : (x ∈ A) ⇔ (x ∈ B)) ⇒ (A = B)

THEOREM NoUniversalSet == ∀ S : ¬(∀ x : x ∈ S)

====