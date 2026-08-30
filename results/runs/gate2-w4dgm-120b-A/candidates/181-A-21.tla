---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite override: Nat is the bounded range the model checker works over,
\* replacing the infinite Nat from Naturals.
NatOverride == 0..MaxNat

\* The theorem from the base spec is assumed here for model checking; it is
\* not proved inside this module.
EvenDoubleBaseTheorem == \A n \in Nat : (2 * n) % 2 = 0

Spec == EvenDoubleBaseTheorem

\* Model initialisation: start verification with a fresh state.
Init == TRUE

\* Every reachable state is the start state; the system never moves.
Next == Init

TypeOK == TRUE

StateConstraint == TRUE

NoAction == TRUE

====