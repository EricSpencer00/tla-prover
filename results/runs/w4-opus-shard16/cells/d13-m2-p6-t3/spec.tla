-------------------------- MODULE W4Od13m2p6t3 --------------------------
EXTENDS Naturals

CONSTANTS Machines

VARIABLES
    phase,      \* coordinator phase: "collecting" | "decided"
    decision,   \* "none" | "commit" | "abort"
    vote,       \* vote[m] : "none" | "yes" | "no"
    mstate      \* mstate[m] : "working" | "prepared" | "committed" | "aborted"

vars == << phase, decision, vote, mstate >>

TypeOK ==
    /\ phase \in {"collecting", "decided"}
    /\ decision \in {"none", "commit", "abort"}
    /\ vote \in [Machines -> {"none", "yes", "no"}]
    /\ mstate \in [Machines -> {"working", "prepared", "committed", "aborted"}]

Init ==
    /\ phase = "collecting"
    /\ decision = "none"
    /\ vote = [m \in Machines |-> "none"]
    /\ mstate = [m \in Machines |-> "working"]

\* A machine votes yes and marks itself prepared (it may be slow to do so).
VoteYes(m) ==
    /\ phase = "collecting"
    /\ vote[m] = "none"
    /\ vote' = [vote EXCEPT ![m] = "yes"]
    /\ mstate' = [mstate EXCEPT ![m] = "prepared"]
    /\ UNCHANGED << phase, decision >>

\* A machine votes no.
VoteNo(m) ==
    /\ phase = "collecting"
    /\ vote[m] = "none"
    /\ vote' = [vote EXCEPT ![m] = "no"]
    /\ UNCHANGED << phase, decision, mstate >>

\* The coordinator commits only when every machine voted yes.
DecideCommit ==
    /\ phase = "collecting"
    /\ \A m \in Machines : vote[m] = "yes"
    /\ decision' = "commit"
    /\ phase' = "decided"
    /\ UNCHANGED << vote, mstate >>

\* The coordinator aborts when at least one machine voted no.
DecideAbort ==
    /\ phase = "collecting"
    /\ \E m \in Machines : vote[m] = "no"
    /\ decision' = "abort"
    /\ phase' = "decided"
    /\ UNCHANGED << vote, mstate >>

\* Under a commit decision, a prepared machine finalises the update.
ApplyCommit(m) ==
    /\ decision = "commit"
    /\ mstate[m] = "prepared"
    /\ mstate' = [mstate EXCEPT ![m] = "committed"]
    /\ UNCHANGED << phase, decision, vote >>

\* Under an abort decision, a machine discards the update.
ApplyAbort(m) ==
    /\ decision = "abort"
    /\ mstate[m] \in {"working", "prepared"}
    /\ mstate' = [mstate EXCEPT ![m] = "aborted"]
    /\ UNCHANGED << phase, decision, vote >>

\* Once every machine has finalised, the coordinator starts a fresh round.
Restart ==
    /\ phase = "decided"
    /\ \A m \in Machines : mstate[m] \in {"committed", "aborted"}
    /\ phase' = "collecting"
    /\ decision' = "none"
    /\ vote' = [m \in Machines |-> "none"]
    /\ mstate' = [m \in Machines |-> "working"]

Next ==
    \/ \E m \in Machines : VoteYes(m)
    \/ \E m \in Machines : VoteNo(m)
    \/ DecideCommit
    \/ DecideAbort
    \/ \E m \in Machines : ApplyCommit(m)
    \/ \E m \in Machines : ApplyAbort(m)
    \/ Restart

Spec == Init /\ [][Next]_vars

\* Atomicity: a committed machine implies a genuine global commit in which
\* every machine voted yes -- no stale participant is committed out of turn.
CommitIsUnanimous ==
    \A m \in Machines :
        (mstate[m] = "committed")
            => (decision = "commit" /\ \A k \in Machines : vote[k] = "yes")

=============================================================================
