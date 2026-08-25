---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(* ----------------------------------------------------------------------
   Backend prover configuration (timeouts, can be assigned in the model)
   ---------------------------------------------------------------------- *)
CONSTANT ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout,
         VeriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout

(* ----------------------------------------------------------------------
   Backend invocation operators (place‑holders for TLAPS pragmas)
   ---------------------------------------------------------------------- *)
Zenon(p)   == TRUE
Isabelle(p)== TRUE
CVC3(p)    == TRUE
Yices(p)   == TRUE
VeriT(p)   == TRUE
Z3(p)      == TRUE
SPASS(p)   == TRUE
LS4(p)     == TRUE

(* ----------------------------------------------------------------------
   Fundamental theorems
   ---------------------------------------------------------------------- *)

(* Set extensionality: two sets are equal iff they have the same elements. *)
SetExtensionality ==
  \A A, B \in SUBSET UNIV :
    (\A x : (x \in A) = (x \in B)) => A = B

(* No set contains every possible value. *)
NoUniversalSet ==
  \A S \in SUBSET UNIV : ~(\A x : x \in S)

(* ----------------------------------------------------------------------
   Temporal‑logic proof‑rule placeholders (names reserved for TLAPS)
   ---------------------------------------------------------------------- *)

InvariantRule(P, Q)      == TRUE
WellFormedRule(P)        == TRUE
StrongFairnessRule(F)    == TRUE
WeakFairnessRule(F)      == TRUE
StepSimulationRule(S)   == TRUE

(* ----------------------------------------------------------------------
   Trivial specification components (required identifiers are none,
   but they are provided for completeness)
   ---------------------------------------------------------------------- *)

SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == {}
PROPERTIES    == {}

====