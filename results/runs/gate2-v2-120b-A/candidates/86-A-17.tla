---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

(* ----------------------------------------------------------------------
   Backend prover configuration operators (no semantics, just placeholders)
   ---------------------------------------------------------------------- *)

(* Zenon prover configuration *)
ZenonTimeout == 30
ZenonInvocation == "zenon"

(* Isabelle prover configuration *)
IsabelleTimeout == 30
IsabelleInvocation == "isabelle"

(* CVC3 prover configuration *)
CVC3Timeout == 30
CVC3Invocation == "cvc3"

(* Yices prover configuration *)
YicesTimeout == 30
YicesInvocation == "yices"

(* veriT prover configuration *)
VeriTTimeout == 30
VeriTInvocation == "verit"

(* Z3 prover configuration *)
Z3Timeout == 30
Z3Invocation == "z3"

(* SPASS prover configuration *)
SPASSTimeout == 30
SPASSInvocation == "spass"

(* LS4 temporal logic prover configuration *)
LS4Timeout == 30
LS4Invocation == "ls4"

(* ----------------------------------------------------------------------
   Temporal logic proof rule placeholders
   ---------------------------------------------------------------------- *)

InvariantRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(* ----------------------------------------------------------------------
   Fundamental theorems stated as TLA+ theorems
   ---------------------------------------------------------------------- *)

SetExtensionality == 
  \A X, Y \in SUBSET UNIV : (\A z \in UNIV : (z \in X) = (z \in Y)) => X = Y

NoUniversalSet == 
  ~(\E X \in SUBSET UNIV : \A y \in UNIV : y \in X)

(* ----------------------------------------------------------------------
   Specification (no state, only theorems)
   ---------------------------------------------------------------------- *)

Spec == SetExtensionality /\ NoUniversalSet

=============================================================================