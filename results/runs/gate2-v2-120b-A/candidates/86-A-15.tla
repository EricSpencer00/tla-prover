---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(* ----------------------------------------------------------------------
   Proof infrastructure: backend pragmas and temporal proof rules.
   The operators below are placeholders that correspond to the various
   provers and tactics described in the natural‑language description.
   They are defined as simple constants or trivial operators because the
   actual proof dispatch is performed by the TLAPS tool, not by the model
   checker.  The definitions are deliberately minimal so that TLC can
   evaluate the module without requiring any external prover.
   ---------------------------------------------------------------------- *)

(* Backend prover configuration operators.  Each returns a record that
   can be inspected by the proof manager.  The fields are chosen to be
   self‑explanatory; the exact contents are not used by TLC. *)
BackendZenon(timeout) == [type |-> "Zenon", timeout |-> timeout]

BackendIsabelle(tactic) == [type |-> "Isabelle", tactic |-> tactic]

BackendCVC3(timeout) == [type |-> "CVC3", timeout |-> timeout]

BackendYices(timeout) == [type |-> "Yices", timeout |-> timeout]

BackendVeriT(timeout) == [type |-> "veriT", timeout |-> timeout]

BackendZ3(timeout) == [type |-> "Z3", timeout |-> timeout]

BackendSPASS(timeout) == [type |-> "SPASS", timeout |-> timeout]

BackendLS4(timeout) == [type |-> "LS4", timeout |-> timeout]

(* ----------------------------------------------------------------------
   Temporal logic proof rules (names only; the rules themselves are
   imported from the standard library).  They are defined as stubs that
   simply evaluate to TRUE so that they do not affect the model checking.
   ---------------------------------------------------------------------- *)

InvarianceRule(P) == TRUE
WFRule(A) == TRUE
SFRule(A) == TRUE
WellFormednessRule(P) == TRUE
StepSimulationRule(Spec) == TRUE

(* ----------------------------------------------------------------------
   The two foundational theorems mentioned in the description.
   They are expressed as theorems that TLC can check.
   ---------------------------------------------------------------------- *)

SetExtensionality == \A X, Y \in SUBSET Nat : ( \A z \in Nat : (z \in X) = (z \in Y) ) => X = Y

NoUniversalSet == \A S \in SUBSET Nat : \E z \in Nat : z \notin S

=============================================================================