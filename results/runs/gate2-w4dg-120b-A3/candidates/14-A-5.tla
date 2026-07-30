---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES pc, cs, ticket

vars == <<pc, cs, ticket>>

TypeOK ==
    /\ pc \in [1..N -> {"idle", "trying", "critical"}]
    /\ cs \in 0..N
    /\ ticket \in [1..N -> 0..MaxNat]

Init ==
    /\ pc = [p \in 1..N |-> "idle"]
    /\ cs = 0
    /\ ticket = [p \in 1..N |-> 0]

Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ UNCHANGED <<cs, ticket>>

Enter(p) ==
    /\ pc[p] = "trying"
    /\ cs = 0
    /\ cs' = p
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED ticket

Exit(p) ==
    /\ pc[p] = "critical"
    /\ cs' = 0
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED ticket

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N :
        (pc[p] = "critical") => (cs = p)

Inv ==
    /\ MutualExclusion
    /\ TypeOK

NatOverride ==
    Nat == [i \in 0..MaxNat |-> i]

StateConstraint == \A p \in 1..N : ticket[p] < MaxNat

====