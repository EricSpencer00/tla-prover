---- MODULE W4Od3m5p5t2 ----
EXTENDS Integers, FiniteSets

Instances == {"A", "B"}
Voters == {"v1", "v2", "v3"}
QUORUM == 2
AMT == 1
INIT == 3
NONE == "none"

VARIABLES phase, votes, approvedLatch, paid, pool

vars == <<phase, votes, approvedLatch, paid, pool>>

Init ==
    /\ phase = "idle"
    /\ votes = [v \in Voters |-> NONE]
    /\ approvedLatch = FALSE
    /\ paid = FALSE
    /\ pool = INIT

\* An instance proposes an irreversible payout from the shared pool, opening a
\* quorum vote.
Propose(i) ==
    /\ phase = "idle"
    /\ phase' = "voting"
    /\ votes' = [v \in Voters |-> NONE]
    /\ UNCHANGED <<approvedLatch, paid, pool>>

\* A voter casts a ballot once per round.
Vote(v, b) ==
    /\ phase = "voting"
    /\ votes[v] = NONE
    /\ votes' = [votes EXCEPT ![v] = b]
    /\ UNCHANGED <<phase, approvedLatch, paid, pool>>

\* A quorum of yes votes permanently latches approval for the payout.
Approve ==
    /\ phase = "voting"
    /\ Cardinality({v \in Voters : votes[v] = "yes"}) >= QUORUM
    /\ approvedLatch' = TRUE
    /\ phase' = "decided"
    /\ UNCHANGED <<votes, paid, pool>>

\* A quorum of no votes ends the round without approval.
Reject ==
    /\ phase = "voting"
    /\ Cardinality({v \in Voters : votes[v] = "no"}) >= QUORUM
    /\ phase' = "decided"
    /\ UNCHANGED <<votes, approvedLatch, paid, pool>>

\* The irreversible payout: executed at most once and only after approval.
Pay ==
    /\ approvedLatch
    /\ ~paid
    /\ pool >= AMT
    /\ pool' = pool - AMT
    /\ paid' = TRUE
    /\ UNCHANGED <<phase, votes, approvedLatch>>

\* Recycle for another round; the approval and payout latches are permanent.
Reset ==
    /\ phase = "decided"
    /\ phase' = "idle"
    /\ UNCHANGED <<votes, approvedLatch, paid, pool>>

Next ==
    \/ \E i \in Instances : Propose(i)
    \/ \E v \in Voters, b \in {"yes", "no"} : Vote(v, b)
    \/ Approve
    \/ Reject
    \/ Pay
    \/ Reset

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ phase \in {"idle", "voting", "decided"}
    /\ votes \in [Voters -> {"yes", "no", NONE}]
    /\ approvedLatch \in BOOLEAN
    /\ paid \in BOOLEAN
    /\ pool \in 0..INIT

\* The irreversible payout is only ever executed after a quorum latched approval,
\* so it never happens without approval and never more than once.
PayOnlyIfApproved == paid => approvedLatch

====