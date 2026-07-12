---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

CONSTANT
    /* No constants are required for this model,
       but the module must compile even with an empty constant set. */

ASSUME CONSTANTS

VARIABLES
    /* No state variables are specified; the module is purely
       for defining constants and properties of the proof system. */

\* ----------------------------------------------------------------------
\*   Identification of backend provers and their configured timeouts
\* ----------------------------------------------------------------------
Provers == {"Zenon", "Isabelle", "CVC3", "Yices", "veriT", "Z3", "SPASS", "LS4"}

Timeouts == [ p \in Provers |-> 0 ]

\* ----------------------------------------------------------------------
\*   Helper predicates for the basic theorems
\* ----------------------------------------------------------------------
SetExtensionality(s, t) ==
    /\ s \in Set
    /\ t \in Set
    /\ (\A x \in Set : (x \in s) <=> (x \in t))

NonUniversalSet(s) ==
    /\ s \in Set
    /\ \E x \in Set : x \notin s

\* ----------------------------------------------------------------------
\*   Operators required by the specification
\* ----------------------------------------------------------------------
\* The specification is trivial because the module only defines constants.
INIT == UNCHANGED <<Provers, Timeouts>>

NEXT == UNCHANGED <<Provers, Timeouts>>

SPECIFICATION == Init /\ [][Next]_<<Provers, Timeouts>>

\* The safety properties requested are the two theorems described.
\* In TLAPS they are represented as invariants that must hold in every state.
INVARIANTS ==
    /\ SetExtensionality(s, t) -> s = t
    /\ \A s \in Set : NonUniversalSet(s)

\* No liveness properties are specified for this module.
PROPERTIES == {}

\* ----------------------------------------------------------------------
\*   Boilerplate for TLC
\* ----------------------------------------------------------------------
THEOREM SetExtensionality_Theorem ==
    [] (SetExtensionality(s, t) -> s = t)

THEOREM NonUniversalSet_Theorem ==
    [] (\A s \in Set : NonUniversalSet(s))

=============================================================================