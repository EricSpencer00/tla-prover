---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*********************************************************************
-- MODULE TLAPS
This module provides a set of dummy operators that represent the
backend configuration for TLAPS and the fundamental temporal logic
rules mentioned in the description.  The operators are defined so
that the module type‑checks and the TLC model checker can be run, but
they do not affect the system state because the specification does
not describe any concrete state variables or actions.

No state variables, initial state, or actions are required; the module
only supplies the identifiers that the reference configuration expects.
*********************************************************************)

\* -----------------------------------------------------------------
\*  No state variables are needed for this specification.
\* -----------------------------------------------------------------
VARIABLES dummy

\* -----------------------------------------------------------------
\*  INITIAL STATE
\* -----------------------------------------------------------------
Init ==
    dummy = 0

\* -----------------------------------------------------------------
\*  NEXT ACTION (does nothing)
\* -----------------------------------------------------------------
Next ==
    UNCHANGED dummy

\* -----------------------------------------------------------------
\*  SPECIFICATION: the usual temporal composition of Init and Next.
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<dummy>>

\* -----------------------------------------------------------------
\*  BACKEND PROVER CONFIGURATION OPERATORS
\*  (These are placeholders; they simply return TRUE so that they can
\*   be referenced in the configuration without causing type errors.)
\* -----------------------------------------------------------------
Zenon(timeout) == TRUE
Isabelle(timeout) == TRUE
CVC3(timeout) == TRUE
Yices(timeout) == TRUE
VeriT(timeout) == TRUE
Z3(timeout) == TRUE
SPASS(timeout) == TRUE
LS4(timeout) == TRUE

\* -----------------------------------------------------------------
\*  TEMPORAL LOGIC RULES (placeholders)
\* -----------------------------------------------------------------
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* -----------------------------------------------------------------
\*  SAFETY PROPERTIES
\* -----------------------------------------------------------------
SetExtensionality ==
    \A X, Y \in SUBSET Nat :
        (\A z \in Nat : (z \in X) <=> (z \in Y)) => X = Y

NoUniversalSet ==
    \A X \in SUBSET Nat : \E y \in Nat : y \notin X

\* -----------------------------------------------------------------
\*  INVARIANTS and PROPERTIES as required by the .cfg
\* -----------------------------------------------------------------
INVARIANTS == { SetExtensionality, NoUniversalSet }
PROPERTIES == {}

\* -----------------------------------------------------------------
\*  THEOREMS (optional, for completeness)
\* -----------------------------------------------------------------
THEOREM SetExtensionalityIsValid == SetExtensionality
THEOREM NoUniversalSetIsValid == NoUniversalSet

=============================================================================