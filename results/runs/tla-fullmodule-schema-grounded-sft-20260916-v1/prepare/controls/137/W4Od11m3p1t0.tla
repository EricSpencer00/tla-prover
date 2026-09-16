---------------------------- MODULE W4Od11m3p1t0 ----------------------------
EXTENDS Naturals

CONSTANTS Nodes, MaxEpoch, MaxV

VARIABLES leader, epoch, total, snap, crashed

vars == <<leader, epoch, total, snap, crashed>>

NoLeader == "none"

TypeOK ==
    /\ leader \in Nodes \cup {NoLeader}
    /\ epoch \in 0..MaxEpoch
    /\ total \in 0..MaxV
    /\ snap \in [Nodes -> 0..MaxV]
    /\ crashed \in SUBSET Nodes

Init ==
    /\ leader = NoLeader
    /\ epoch = 0
    /\ total = 0
    /\ snap = [n \in Nodes |-> 0]
    /\ crashed = {}

Elect(n) ==
    /\ n \notin crashed
    /\ (n # leader \/ epoch < MaxEpoch)
    /\ leader' = n
    /\ epoch' = IF epoch < MaxEpoch THEN epoch + 1 ELSE epoch
    /\ snap' = [snap EXCEPT ![n] = total]
    /\ UNCHANGED <<total, crashed>>

Write ==
    /\ leader # NoLeader
    /\ leader \notin crashed
    /\ snap[leader] < MaxV
    /\ total' = snap[leader] + 1
    /\ snap' = [snap EXCEPT ![leader] = snap[leader] + 1]
    /\ UNCHANGED <<leader, epoch, crashed>>

StepDown ==
    /\ leader # NoLeader
    /\ leader' = NoLeader
    /\ UNCHANGED <<epoch, total, snap, crashed>>

Crash(n) ==
    /\ n \notin crashed
    /\ (crashed \cup {n}) # Nodes
    /\ crashed' = crashed \cup {n}
    /\ UNCHANGED <<leader, epoch, total, snap>>

Next ==
    \/ \E n \in Nodes : Elect(n)
    \/ Write
    \/ StepDown
    \/ \E n \in Nodes : Crash(n)

Spec == Init /\ [][Next]_vars

NoLostUpdate ==
    leader # NoLeader => snap[leader] = total

=============================================================================