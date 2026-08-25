---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Backend prover placeholders – they simply return their argument.
  In TLAPS these names are used to direct proof obligations.
-----------------------------------------------------------------*)
Zenon(p)   == p
Isabelle(p)== p
CVC3(p)    == p
Yices(p)   == p
VeriT(p)   == p
Z3(p)      == p
SPASS(p)   == p
LS4(p)     == p

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule stubs – reserved names.
-----------------------------------------------------------------*)
InvarianceRule       == TRUE
WellFormednessRule  == TRUE
StrongFairnessRule  == TRUE
WeakFairnessRule    == TRUE
StepSimulationRule  == TRUE

(*-----------------------------------------------------------------
  Foundational theorems required by the description.
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A A, B \in SUBSET UNIV :
    (\A x \in UNIV : (x \in A) <=> (x \in B)) => A = B

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV : S # UNIV

(*-----------------------------------------------------------------
  Required identifiers referenced by the (empty) .cfg file.
-----------------------------------------------------------------*)
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == {}
PROPERTIES    == {}

====