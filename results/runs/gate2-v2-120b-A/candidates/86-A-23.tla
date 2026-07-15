---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (none required by the .cfg, but we keep the section for clarity)
\* ----------------------------------------------------------------------
CONSTANTS

\* ----------------------------------------------------------------------
\* State variables
\* (The description specifies that there are no state variables)
\* ----------------------------------------------------------------------
VARIABLES

\* ----------------------------------------------------------------------
\* Helper definitions (set of all values of interest)
\* ----------------------------------------------------------------------
AllVals == Nat \cup STRING \cup BOOLEAN

\* ----------------------------------------------------------------------
\* Temporal logic proof rules (axioms) – names are reserved for later use.
\* They are stated as theorems but have no effect on the model checking.
\* ----------------------------------------------------------------------
AXIOM SetExtensionality ==
  \A S, T \in SUBSET AllVals :
    (\A x \in AllVals : (x \in S) = (x \in T)) => S = T

AXIOM NoUniversalSet ==
  ~(\A x \in AllVals : TRUE)

\* ----------------------------------------------------------------------
\* Specification (no variables, so the trivial specification)
\* ----------------------------------------------------------------------
Specification == TRUE

Init == TRUE

Next == UNCHANGED <<>>   \* no state change possible

\* ----------------------------------------------------------------------
\* Theorems that capture the proof rules (again, no effect on the model)
\* ----------------------------------------------------------------------
THEOREM SetExtensionalityIsValid == SetExtensionality
THEOREM NoUniversalSetIsValid == NoUniversalSet

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg (they are defined but trivially true)
\* ----------------------------------------------------------------------
SPECIFICATION == Specification

INIT == Init

NEXT == Next

INVARIANTS == { SetExtensionality, NoUniversalSet }

PROPERTIES == { SetExtensionality }

====