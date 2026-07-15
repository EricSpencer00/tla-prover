---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat
CONSTANT Nat

\* Override the infinite set of naturals with a finite bounded set
Nat == 0 .. MaxNat

VARIABLES x

\* Initial state: choose any natural number in the bounded range
Init ==
    /\ x \in Nat

\* The only action is to increment x while staying within the bound
Next ==
    /\ x < MaxNat
    /\ x' = x + 1

\* Safety invariant: the double of any reachable value of x is even
EvenDouble ==
    2 * x % 2 = 0

\* Safety invariant: x always stays within the bounded natural set
Bounded ==
    x \in Nat

\* The full specification
Spec ==
    Init /\ [][Next]_<<x>>

\* The set of invariants required by the .cfg
INVARIANT == /\ EvenDouble /\ Bounded

=============================================================================