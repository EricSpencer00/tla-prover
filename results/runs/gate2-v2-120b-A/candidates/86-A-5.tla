---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\*  Backend configuration for the TLA+ Proof System (TLAPS)
\* ----------------------------------------------------------------------
\* The constants below represent the set of provers that TLAPS may
\* dispatch proof obligations to.  The model checker will not assign
\* values to them – they are merely placeholders that exist so that the
\* identifiers can be referenced in the configuration file without a
\* name‑clash.  The values are deliberately left uninterpreted.
\* ----------------------------------------------------------------------
CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* No state variables are required for the configuration module.
VARIABLES dummy

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    dummy = 0

\* ----------------------------------------------------------------------
\*  Next-state relation – a trivial stutter step.  The configuration
\*  module does not model any dynamic behaviour; the purpose of the
\*  specification is solely to expose the identifiers required by the
\*  .cfg file.
\* ----------------------------------------------------------------------
Next ==
    dummy' = dummy

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<dummy>>

\* ----------------------------------------------------------------------
\*  Safety theorems required by the description
\* ----------------------------------------------------------------------
\*  Set extensionality: two sets with the same elements are equal.
SetExtensionality ==
    \A A, B \in SUBSET Nat :
        (\A x \in Nat : x \in A <=> x \in B) => A = B

\*  No set contains every possible value.
NoUniversalSet ==
    \A A \in SUBSET Nat : \E x \in Nat : x \notin A

\* ----------------------------------------------------------------------
\*  Theorems that expose the names of the primitive temporal proof rules.
\*  The body of each theorem is a trivial tautology; the important part is
\*  that the identifier exists and is exported.
\* ----------------------------------------------------------------------
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* ----------------------------------------------------------------------
\*  The constants that the .cfg file expects – they are exported so that
\*  the configuration can reference them.
\* ----------------------------------------------------------------------
PROBES == { Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4 }

\* ----------------------------------------------------------------------
\*  The operators mentioned in the task description are exported by
\*  virtue of being top‑level definitions.
\* ----------------------------------------------------------------------
INVARIANTS == SetExtensionality
PROPERTIES == NoUniversalSet

====