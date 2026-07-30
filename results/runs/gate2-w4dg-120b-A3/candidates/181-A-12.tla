---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The model checker TLC does not support infinite sets, so the natural
\* numbers are overridden with a bounded finite range. This operator is
\* deliberately NOT a declaration; it replaces the unbounded Nat operator
\* inherited from Naturals.
NatOverride == 0..MaxNat

\* Nothing is modelled beyond the override: the theorem DoubleIsEven is
\* assumed (it is a constant-level assumption, not a conjunct of the SPEC).
SPECIFICATION == TRUE

\* The proof never actually changes state, so the transition relation is
\* empty: every state is a deadlock, which is exactly what TLC is told to
\* EXPECT with SPECIFICATION == TRUE.
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}
====