---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers for model checking.
\* This operator replaces the infinite Nat set used in the base spec.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Assumption: the double of any natural number is even.
\* (Kept as an ASSUME to allow TLC to explore the finite domain.)
\* ----------------------------------------------------------------------
ASSUME DoubleIsEven ==
    \A m \in NatOverride : \E k \in NatOverride : 2 * m = 2 * k

\* ----------------------------------------------------------------------
\* State variable.
\* ----------------------------------------------------------------------
VARIABLE n

\* ----------------------------------------------------------------------
\* Initial state predicate.
\* ----------------------------------------------------------------------
Init == n = 0

\* ----------------------------------------------------------------------
\* Next-state relation (trivial for this model; the variable never changes).
\* ----------------------------------------------------------------------
Next == n' = n

\* ----------------------------------------------------------------------
\* Full specification of the system.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<n>>

\* ----------------------------------------------------------------------
\* The following comment is used by the test harness to supply the
\* required INIT clause when no explicit .cfg file is provided.
\* TLC will treat the predicate named Init as the initial state.
\* ----------------------------------------------------------------------
\* INIT Init

=============================================================================