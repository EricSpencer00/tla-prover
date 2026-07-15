---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend pragma operators for TLAPS (no operational effect, used only for
\* proof configuration).  They are defined as simple nullary operators.
\* ----------------------------------------------------------------------
Zenon   == TRUE
Isabelle == TRUE
CVC3    == TRUE
Yices   == TRUE
VeriT   == TRUE
Z3      == TRUE
SPASS   == TRUE
LS4     == TRUE

\* ----------------------------------------------------------------------
\* Temporal proof rule names (reserved, no operational effect).
\* ----------------------------------------------------------------------
Extensionality == 
  \E X, Y \in SUBSET Nat : X = Y

NoUniversalSet == 
  \A x \in Nat : x \notin Nat

\* ----------------------------------------------------------------------
\* Variables (the system has none, but a dummy variable is introduced so
\* that the module has a non‑empty state for TLC to explore).
\* ----------------------------------------------------------------------
VARIABLE dummy

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init == dummy = 0

\* ----------------------------------------------------------------------
\* Next-state action (does nothing, keeps dummy unchanged)
\* ----------------------------------------------------------------------
Next == dummy' = dummy

\* ----------------------------------------------------------------------
\* Stuttering step (required because there are no real actions)
\* ----------------------------------------------------------------------
Stutter == UNCHANGED dummy

\* ----------------------------------------------------------------------
\* Specification (full behavior)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next \/ Stutter]_<<dummy>>

\* ----------------------------------------------------------------------
\* Safety invariants (theorems) required by the description
\* ----------------------------------------------------------------------
SetExtensionality == \A A, B \subseteq Nat :
                       (\A x \in Nat : (x \in A) = (x \in B)) => A = B

NoUniversalSetThm == \A x \in Nat : x \notin Nat

=============================================================================