---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

CONSTANTS Chosen, InCS

\* NatOverride is a no-op that exists so the .cfg file can substitute it for Nat.
NatOverride == Nat

VARIABLES chosen, inCS

vars == <<chosen, inCS>>

TypeOK == chosen \in [1..N -> 0..MaxNat] /\ inCS \subseteq (1..N)

MutualExclusion == \A p, q \in (1..N) : (p \in inCS /\ q \in inCS) => p = q

Init == chosen = [p \in 1..N |-> 0] /\ inCS = {}

\* The Bakery algorithm actions are exactly those from the baseline spec;
\* this module adds no new actions and changes nothing about them.
Bump(p) == chosen' = [chosen EXCEPT ![p] = (chosen[p] + 1) % (MaxNat + 1)]
             /\ UNCHANGED inCS

Enter(p) == inCS' = inCS \cup {p} /\ UNCHANGED chosen

Exit(p) == inCS' = inCS \ {p} /\ UNCHANGED chosen

Next == \E p \in 1..N : Bump(p) \/ Enter(p) \/ Exit(p)

ISpec == Init /\ [][Next]_vars

Inv == TypeOK /\ MutualExclusion

====