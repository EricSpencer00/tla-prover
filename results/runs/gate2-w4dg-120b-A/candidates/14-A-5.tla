---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

Procs == {"p1", "p2", "p3"}

VARIABLES pc, ticket

vars == <<pc, ticket>>

TypeOK ==
    /\ pc \in [Procs -> {"idle", "trying", "cs"}]
    /\ ticket \in [Procs -> 0..MaxNat]

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ ticket = [p \in Procs |-> 0]

Request(n) ==
    /\ pc[n] = "idle"
    /\ pc' = [pc EXCEPT ![n] = "trying"]
    /\ UNCHANGED ticket

Enter(n) ==
    /\ pc[n] = "trying"
    /\ \A m \in Procs : pc[m] # "cs"
    /\ ticket' = [ticket EXCEPT ![n] = IF ticket[n] < MaxNat THEN ticket[n] + 1 ELSE ticket[n]]
    /\ pc' = [pc EXCEPT ![n] = "cs"]

Exit(n) ==
    /\ pc[n] = "cs"
    /\ pc' = [pc EXCEPT ![n] = "idle"]
    /\ UNCHANGED ticket

Next ==
    \/ \E n \in Procs : Request(n)
    \/ \E n \in Procs : Enter(n)
    \/ \E n \in Procs : Exit(n)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A n1 \in Procs, n2 \in Procs :
        (pc[n1] = "cs" /\ pc[n2] = "cs") => n1 = n2

Inv ==
    /\ \A p \in Procs : ticket[p] >= 0
    /\ \A p \in Procs : pc[p] = "cs" => ticket[p] < MaxNat

====