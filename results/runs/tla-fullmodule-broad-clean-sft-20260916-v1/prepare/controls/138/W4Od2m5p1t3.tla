---- MODULE W4Od2m5p1t3 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Updates, Quorum

VARIABLES votes, applied, acked, slow

vars == <<votes, applied, acked, slow>>

Init ==
    /\ votes = [u \in Updates |-> {}]
    /\ applied = {}
    /\ acked = {}
    /\ slow = {}

Vote(n, u) ==
    /\ n \notin slow
    /\ n \notin votes[u]
    /\ votes' = [votes EXCEPT ![u] = @ \cup {n}]
    /\ UNCHANGED <<applied, acked, slow>>

BecomeSlow(n) ==
    /\ n \notin slow
    /\ slow' = slow \cup {n}
    /\ UNCHANGED <<votes, applied, acked>>

SpeedUp(n) ==
    /\ n \in slow
    /\ slow' = slow \ {n}
    /\ UNCHANGED <<votes, applied, acked>>

Commit(u) ==
    /\ u \notin applied
    /\ Cardinality(votes[u]) >= Quorum
    /\ applied' = applied \cup {u}
    /\ UNCHANGED <<votes, acked, slow>>

Ack(u) ==
    /\ u \in applied
    /\ u \notin acked
    /\ acked' = acked \cup {u}
    /\ UNCHANGED <<votes, applied, slow>>

Next ==
    \/ \E n \in Nodes, u \in Updates : Vote(n, u)
    \/ \E n \in Nodes : BecomeSlow(n) \/ SpeedUp(n)
    \/ \E u \in Updates : Commit(u) \/ Ack(u)

Spec == Init /\ [][Next]_vars

NoLostUpdate ==
    acked \subseteq applied
====