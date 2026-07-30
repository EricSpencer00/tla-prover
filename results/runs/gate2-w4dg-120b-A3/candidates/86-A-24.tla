---- MODULE TLAPS ----
EXTENDS Naturals

(* TLAPS backend configuration: operators that name the backends the proof      *)
(* engine may invoke, together with admissible timeouts and tactics.  The      *)
(* module also records the two foundational set-theoretic theorems, reserved    *)
(* here so they cannot be introduced again elsewhere.                           *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

Created == "2026-07-30"

TypeOK ==
  /\ Zenon \in {1, 2}
  /\ Isabelle \in {1, 2}
  /\ CVC3 \in {1, 2}
  /\ Yices \in {1, 2}
  /\ veriT \in {1, 2}
  /\ Z3 \in {1, 2}
  /\ SPASS \in {1, 2}
  /\ LS4 \in {1, 2}

\* The module carries no state of its own, so the SPECIFICATION trivially
\* delegates everything to the empty NEXT.
Rewrite(using, timeout, tactic) == [using |-> using, timeout |-> timeout, tactic |-> tactic]

InitZenon == Rewrite(Zenon, 1, "default")
InitIsabelle == Rewrite(Isabelle, 1, "default")
InitCVC3 == Rewrite(CVC3, 1, "default")
InitYices == Rewrite(Yices, 1, "default")
InitVeriT == Rewrite(veriT, 1, "default")
InitZ3 == Rewrite(Z3, 1, "default")
InitSPASS == Rewrite(SPASS, 1, "default")
InitLS4 == Rewrite(LS4, 1, "default")

InitAll ==
  /\ InitZenon
  /\ InitIsabelle
  /\ InitCVC3
  /\ InitYices
  /\ InitVeriT
  /\ InitZ3
  /\ InitSPASS
  /\ InitLS4

Next == InitAll

SpecInit == InitAll
SpecNext == Next
Spec == SpecInit /\ [][SpecNext]_<<>>
Init == SpecInit
NextStep == SpecNext
Spec == Spec

SetExtensionality == \A A, B \in SUBSET Naturals : (\A x \in Naturals : x \in A <=> x \in B) => A = B
NoUniversalSet == \A S \in SUBSET Naturals : \A x \in Naturals : x \in S => FALSE

SpecHolds == Spec
InvariantsHold == Spec
PropertiesHold == Spec

====