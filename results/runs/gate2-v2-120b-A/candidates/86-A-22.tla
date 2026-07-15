---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(*--------------------------------------------------------------------
  Backend configuration: each constant represents a prover backend.
  The values are symbolic identifiers; the actual configuration is
  supplied by the .cfg file used with TLC.
--------------------------------------------------------------------*)

(* Pragma definitions that tell TLAPS which backend to use.
   These are simple operators that return the corresponding constant. *)
ZenonBackend == Zenon
IsabelleBackend == Isabelle
CVC3Backend == CVC3
YicesBackend == Yices
VeriTBackend == VeriT
Z3Backend == Z3
SPASSBackend == SPASS
LS4Backend == LS4

(* Time‑out and tactic parameters – fixed symbolic constants. *)
Timeout == 10               \* seconds
DefaultTactic == "default"

(* A dummy variable used only to give the module a non‑trivial state. *)
VARIABLE dummy

(*--------------------------------------------------------------------
  SPECIFICATION
--------------------------------------------------------------------*)
SPECIFICATION == 
   /\ dummy \in {0,1}
   /\ dummy' = dummy

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init == dummy = 0

(*--------------------------------------------------------------------
  Next-state relation – does nothing but keep the state unchanged.
--------------------------------------------------------------------*)
Next == UNCHANGED dummy

(*--------------------------------------------------------------------
  Invariant that must hold in every reachable state.
--------------------------------------------------------------------*)
Inv == dummy \in {0,1}

(*--------------------------------------------------------------------
  Safety property: set extensionality (axiom) and the claim that no
  set contains every possible value.  We expose them as theorems that
  can be used by downstream proofs.
--------------------------------------------------------------------*)
SetExtensionality == \A A, B \subseteq UNIV : (\A x : x \in A <=> x \in B) => A = B

NoUniversalSet == \A S : S # UNIV

(*--------------------------------------------------------------------
  Exported operators required by the description.
--------------------------------------------------------------------*)
THEOREM SetExtThm == SetExtensionality
THEOREM NoUSetThm == NoUniversalSet

====