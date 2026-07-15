---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  Constants (no specific values are required for this configuration)   *)
(***************************************************************************)
CONSTANTS
    timeout,            \* Timeout (in seconds) for automated provers
    maxInvocations      \* Maximum number of prover invocations allowed

(***************************************************************************)
(*  Backend pragma operators for TLAPS                                    *)
(***************************************************************************)

Zenon(p) == Axiom   \* Dispatch proof obligation p to Zenon prover
Isabelle(p) == Axiom   \* Dispatch p to Isabelle
CVC3(p) == Axiom   \* Dispatch p to CVC3
Yices(p) == Axiom   \* Dispatch p to Yices
VeriT(p) == Axiom   \* Dispatch p to veriT
Z3(p) == Axiom   \* Dispatch p to Z3
SPASS(p) == Axiom   \* Dispatch p to SPASS
LS4(p) == Axiom   \* Dispatch p to LS4 temporal prover

(***************************************************************************)
(*  Temporal logic proof rules (names reserved for future reference)      *)
(***************************************************************************)

(* Invariance rule: if Init => Inv and Inv /\ [Next]_vars => Inv, then Inv holds *)
InvRule ==
  /\ Init => Inv
  /\ (Inv /\ [Next]_vars) => Inv

(* Strong fairness rule placeholder *)
StrongFairness == TRUE

(* Weak fairness rule placeholder *)
WeakFairness == TRUE

(* Well‑formedness rule placeholder *)
WellFormedness == TRUE

(***************************************************************************)
(*  Fundamental theorems                                                  *)
(***************************************************************************)

SetExtensionality ==
  \A X, Y \in SUBSET Nat : (\A e \in Nat : e \in X <=> e \in Y) => X = Y

NoUniversalSet ==
  \A S \in SUBSET Nat : \E x \in Nat : x \notin S

(***************************************************************************)
(*  Specification (trivial, since the module provides no state)           *)
(***************************************************************************)

(* No state variables are needed; the model is empty *)
Spec == TRUE

Init == Spec
Next == Spec
INVARIANTS == { SetExtensionality, NoUniversalSet }
PROPERTIES == SetExtensionality

=============================================================================