---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

ASSUME MaxNat \in Nat \ {0}

VARIABLES state, id, pc, serving, snapshot

vars == <<state, id, pc, serving, snapshot>>

TypeOK ==
    /\ state \in [1..N -> {"idle", "waiting", "critical"}]
    /\ id \in [1..N -> 0..MaxNat]
    /\ pc \in [1..N -> {"idle", "waiting", "critical", "done"}]
    /\ serving \in [1..N -> 0..MaxNat]
    /\ snapshot \in [1..N -> 0..MaxNat]

Init ==
    /\ state = [p \in 1..N |-> "idle"]
    /\ id = [p \in 1..N |-> 0]
    /\ pc = [p \in 1..N |-> "idle"]
    /\ serving = [q \in 1..N |-> 0]
    /\ snapshot = [p \in 1..N |-> 0]

Request(p) ==
    /\ state[p] = "idle"
    /\ pc[p] = "idle"
    /\ \E k \in 0..MaxNat :
        /\ id' = [id EXCEPT ![p] = k]
        /\ serving' = [serving EXCEPT ![p] = k]
    /\ state' = [state EXCEPT ![p] = "waiting"]
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ snapshot' = [snapshot EXCEPT ![p] = 0]

View(p) ==
    /\ state[p] = "waiting"
    /\ pc[p] = "waiting"
    /\ \A q \in 1..N :
        /\ IF pc[q] = "critical"
            THEN snapshot' = [snapshot EXCEPT ![p] = serving[q]]
            ELSE snapshot' = [snapshot EXCEPT ![p] = snapshot[p]]
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<state, id, serving>>

Enter(p) ==
    /\ state[p] = "waiting"
    /\ pc[p] = "critical"
    /\ \A q \in 1..N : id[p] <= serving[q]
    /\ state' = [state EXCEPT ![p] = "critical"]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<id, serving, snapshot>>

Exit(p) ==
    /\ state[p] = "critical"
    /\ pc[p] = "done"
    /\ state' = [state EXCEPT ![p] = "idle"]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<id, serving, snapshot>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : View(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Inv ==
    /\ state = [p \in 1..N |-> IF pc[p] = "critical" THEN "critical" ELSE state[p]]
    /\ id \in [1..N -> 0..MaxNat]
    /\ pc \in [1..N -> {"idle", "waiting", "critical", "done"}]
    /\ serving \in [1..N -> 0..MaxNat]
    /\ snapshot \in [1..N -> 0..MaxNat]

MutualExclusion ==
    \A p, q \in 1..N : (state[p] = "critical" /\ state[q] = "critical") => p = q

ISpec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N : Request(p))
    /\ WF_vars(\E p \in 1..N : View(p))
    /\ WF_vars(\E p \in 1..N : Enter(p))
    /\ WF_vars(\E p \in 1..N : Exit(p))

====