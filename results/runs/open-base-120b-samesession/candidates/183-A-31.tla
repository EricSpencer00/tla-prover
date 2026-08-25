---- MODULE TLAPS ----
EXTENDS TLC, FiniteSets

(*-----------------------------------------------------------------
  Backend provers and their configuration parameters.
  These constants are used by TLAPS to select the appropriate
  automated theorem prover or SMT solver.
-----------------------------------------------------------------*)
CONSTANT Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4
CONSTANT ZenonTimeout, IsabelleTimeout, CVC3Timeout,
         YicesTimeout, VeriTTimeout, Z3Timeout,
         SPASSTimeout, LS4Timeout

(*-----------------------------------------------------------------
  Fundamental set-theoretic theorems that are always available.
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x \in UNIV : x \notin S

(*-----------------------------------------------------------------
  Temporal‑logic proof rules (place‑holders).  Their names are
  reserved for use by the proof system; the definitions below are
  intentionally trivial.
-----------------------------------------------------------------*)
InvarianceRule ==
  TRUE

WellFormednessRule ==
  TRUE

StrongFairnessRule ==
  TRUE

WeakFairnessRule ==
  TRUE

StepSimulationRule ==
  TRUE

====