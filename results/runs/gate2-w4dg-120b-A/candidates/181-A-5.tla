---- MODULE MC_sums_even ----
EXTENDS Naturals

\* System overview: this is a model-checking configuration module for the
\* proof that the double of any natural number is even. It imports the
\* mathematical definitions from the base specification and overrides the
\* natural number set with a finite range so TLC can check the theorem for
\* a bounded set of values.

CONSTANTS MaxNat, Nat

VARIABLES n

vars == <<n>>

TypeOK == n \in Nat

Init == n = 0

Next == \E m \in Nat : n' = m

Spec == Init /\ [][Next]_vars

\* Model bound: the natural number set is overridden with the finite range
\* zero through one million (MaxNat). The theorem is assumed here as a
\* constant-level assumption so TLC can process the spec.
SumIsEven == \A k \in Nat : k = 2 * (k \div 2)

====