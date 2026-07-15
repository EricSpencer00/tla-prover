---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be bound in the .cfg file)
\*   MaxNat : the maximum natural number to consider
\*   Nat    : the finite set of natural numbers from 0 to MaxNat inclusive
\* ----------------------------------------------------------------------
CONSTANT MaxNat, Nat

\* ----------------------------------------------------------------------
\* State variable
\*   n : a natural number chosen from Nat
\* ----------------------------------------------------------------------
VARIABLE n

\* ----------------------------------------------------------------------
\* Derived constant: the double of a natural number
\* ----------------------------------------------------------------------
Double(m) == 2 * m

\* ----------------------------------------------------------------------
\* Safety invariant: every double is even
\* An integer is even iff it is a multiple of 2.
\* ----------------------------------------------------------------------
Even(x) == x % 2 = 0

DoubleIsEven == Even(Double(n))

\* ----------------------------------------------------------------------
\* Initial predicate
\*   n is any element of the bounded natural set Nat
\* ----------------------------------------------------------------------
Init == n \in Nat

\* ----------------------------------------------------------------------
\* No-op action that lets TLC explore the state space without changing n.
\* This is sufficient because the only property we are checking is a
\* state invariant that must hold in every reachable state.
\* ----------------------------------------------------------------------
Next == UNCHANGED n

\* ----------------------------------------------------------------------
\* Specification operator required by the configuration
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<n>>

\* ----------------------------------------------------------------------
\* The name expected by the .cfg for the invariant
\* ----------------------------------------------------------------------
INVARIANT == DoubleIsEven

\* ----------------------------------------------------------------------
\* Optional properties (placeholders to satisfy the required identifiers)
\* They are defined as true, meaning they impose no additional constraints.
\* ----------------------------------------------------------------------
PROPERTIES == TRUE
SAFETY == TRUE
LIVENESS == TRUE

====