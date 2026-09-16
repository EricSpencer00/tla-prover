---------------------------- MODULE W4Od17m2p5t0 ----------------------------
EXTENDS Naturals

CONSTANTS Participants, Bags, NoBag

Votes == {"none", "yes", "no"}

VARIABLES pc, votes, crashed, cur, dispatched
vars == <<pc, votes, crashed, cur, dispatched>>

TypeOK ==
    /\ pc \in {"idle", "voting", "committed", "aborted"}
    /\ votes \in [Participants -> Votes]
    /\ crashed \subseteq Participants
    /\ cur \in Bags \cup {NoBag}
    /\ dispatched \subseteq Bags

Init ==
    /\ pc = "idle"
    /\ votes = [p \in Participants |-> "none"]
    /\ crashed = {}
    /\ cur = NoBag
    /\ dispatched = {}

StartTxn(b) ==
    /\ pc = "idle"
    /\ b \notin dispatched
    /\ cur' = b
    /\ pc' = "voting"
    /\ votes' = [p \in Participants |-> "none"]
    /\ UNCHANGED <<crashed, dispatched>>

Crash(p) ==
    /\ crashed = {}
    /\ crashed' = {p}
    /\ UNCHANGED <<pc, votes, cur, dispatched>>

CastVote(p, v) ==
    /\ pc = "voting"
    /\ p \notin crashed
    /\ votes[p] = "none"
    /\ v \in {"yes", "no"}
    /\ votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED <<pc, crashed, cur, dispatched>>

CommitDecide ==
    /\ pc = "voting"
    /\ crashed = {}
    /\ \A p \in Participants : votes[p] = "yes"
    /\ pc' = "committed"
    /\ dispatched' = dispatched \cup {cur}
    /\ UNCHANGED <<votes, crashed, cur>>

AbortDecide ==
    /\ pc = "voting"
    /\ ( (\E p \in Participants : votes[p] = "no") \/ crashed # {} )
    /\ pc' = "aborted"
    /\ UNCHANGED <<votes, crashed, cur, dispatched>>

Finish ==
    /\ pc \in {"committed", "aborted"}
    /\ pc' = "idle"
    /\ cur' = NoBag
    /\ UNCHANGED <<votes, crashed, dispatched>>

Reopen(b) ==
    /\ pc = "idle"
    /\ b \in dispatched
    /\ dispatched' = dispatched \ {b}
    /\ UNCHANGED <<pc, votes, crashed, cur>>

Next ==
    \/ \E b \in Bags : StartTxn(b)
    \/ \E p \in Participants : Crash(p)
    \/ \E p \in Participants, v \in Votes : CastVote(p, v)
    \/ CommitDecide
    \/ AbortDecide
    \/ Finish
    \/ \E b \in Bags : Reopen(b)

Spec == Init /\ [][Next]_vars

TwoPCSafe ==
    /\ (pc = "committed" => \A p \in Participants : votes[p] = "yes")
    /\ (pc = "voting" => cur \notin dispatched)
============================================================================