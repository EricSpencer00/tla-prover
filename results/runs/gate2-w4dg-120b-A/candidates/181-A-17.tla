---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

VARIABLES x

vars == <<x>>

TypeOK == /\ MaxNat \in Nat
          /\ x \in Nat

Init == /\ MaxNat = 1_000_000
        /\ x = 0

Next == /\ x < MaxNat
        /\ x' = x + 1
        /\ UNCHANGED <<>>

Spec == Init /\ [][Next]_vars

\* The theorem from the base specification is assumed as a constant-level
\* assumption: for every natural number, its double is even. This model is
\* bounded so TLC can check the consequences of that assumption.
AssumeTheory == \A n \in 0..MaxNat : (2 * n) % 2 = 0

====