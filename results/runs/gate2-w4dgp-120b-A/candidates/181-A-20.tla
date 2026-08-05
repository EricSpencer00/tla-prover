---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == 0..MaxNat

ASSUME MaxNat \in Nat /\ MaxNat >= 1

VARIABLES n
vars == <<n>>

Init == n = 0
Step == n < MaxNat /\ n' = n + 1
Idle == n = MaxNat /\ UNCHANGED n

Next == Step \/ Idle

Spec == Init /\ [][Next]_vars

EvenDoubles == \A x \in NatOverride : (2 * x) % 2 = 0
====