---- MODULE MC_sums_even ----
EXTENDS Naturals, Sequences, TLC

CONSTANT MaxNat, Nat

\* ----------------------------------------------------------------------
\* The base specification is assumed to provide the theorem that
\* the double of any natural number is even.  Here we model‑check that
\* theorem for a finite set of natural numbers.
\* ----------------------------------------------------------------------
VARIABLE x

\* The finite domain of natural numbers for model checking
NatSet == Nat

\* ----------------------------------------------------------------------
\* Init: start with any value in the bounded natural-number set
\* ----------------------------------------------------------------------
Init ==
    /\ x \in NatSet

\* ----------------------------------------------------------------------
\* Next: nondeterministically move to any (possibly the same) value
\* in the bounded set.  This keeps the model simple while
\* exercising all reachable states.
\* ----------------------------------------------------------------------
Next ==
    /\ x' \in NatSet

\* ----------------------------------------------------------------------
\* Safety invariant: every reachable state satisfies the theorem that
\* the double of x is even.  The predicate Even(y) expresses that y
\* is divisible by 2.
\* ----------------------------------------------------------------------
Even(y) == y % 2 = 0

SafetyInv == Even(2 * x)

\* ----------------------------------------------------------------------
\* Constants and specifications required by the .cfg file
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<x>>
INV == SafetyInv
PROP == SafetyInv

=============================================================================