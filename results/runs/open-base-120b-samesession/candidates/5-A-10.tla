---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    vote,           \* [p \in participants -> {yes,no}]
    alive,          \* [p \in participants -> BOOLEAN]
    final,          \* [p \in participants -> {undecided, commit, abort}]
    sentVote,       \* [p \in participants -> BOOLEAN]
    requestSent,    \* [p \in participants -> BOOLEAN]   \* coordinator side
    recvVote,       \* [p \in participants -> {yes,no,waiting}]
    decision,       \* {undecided, commit, abort}   \* coordinator's own decision
    broadcastSent,  \* [p \in participants -> {commit,abort,notsent}]
    coordAlive      \* BOOLEAN  (coordinator is alive)

vars == << vote, alive, final, sentVote, requestSent, recvVote,
           decision, broadcastSent, coordAlive >>

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ final \in [participants -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ decision \in {undecided, commit, abort}
    /\ broadcastSent \in [participants -> {commit, abort, notsent}]
    /\ coordAlive \in BOOLEAN

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ \A p \in participants:
          /\ vote[p] \in {yes, no}
          /\ alive[p] = TRUE
          /\ final[p] = undecided
          /\ sentVote[p] = FALSE
    /\ \A p \in participants: requestSent[p] = FALSE
    /\ \A p \in participants: recvVote[p] = waiting
    /\ decision = undecided
    /\ \A p \in participants: broadcastSent[p] = notsent
    /\ coordAlive = TRUE

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendRequest(p) ==
    /\ coordAlive
    /\ ~requestSent[p]
    /\ UNCHANGED << vote, alive, final, sentVote, recvVote, decision,
                    broadcastSent, coordAlive >>
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]

ReceiveVote(p) ==
    /\ coordAlive
    /\ decision = undecided
    /\ requestSent[p]
    /\ recvVote[p] = waiting
    /\ sentVote[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, alive, final, sentVote, requestSent,
                    decision, broadcastSent, coordAlive >>

DetectFault(p) ==
    /\ coordAlive
    /\ decision = undecided
    /\ requestSent[p]
    /\ recvVote[p] = waiting
    /\ ~alive[p]          \* participant crashed before sending vote
    /\ ~sentVote[p]
    /\ decision' = abort
    /\ UNCHANGED << vote, alive, final, sentVote, requestSent,
                    recvVote, broadcastSent, coordAlive >>

MakeDecision ==
    /\ coordAlive
    /\ decision = undecided
    /\ \A p \in participants: requestSent[p]
    /\ \A p \in participants: recvVote[p] # waiting
    /\ IF \A p \in participants: recvVote[p] = yes
          THEN decision' = commit
          ELSE decision' = abort
    /\ UNCHANGED << vote, alive, final, sentVote, requestSent,
                    recvVote, broadcastSent, coordAlive >>

Broadcast(p) ==
    /\ coordAlive
    /\ decision \in {commit, abort}
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = decision]
    /\ UNCHANGED << vote, alive, final, sentVote, requestSent,
                    recvVote, decision, coordAlive >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED << vote, alive, final, sentVote, requestSent,
                    recvVote, decision, broadcastSent >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ alive[p]
    /\ requestSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, final, requestSent, recvVote,
                    decision, broadcastSent, coordAlive >>

AbortOnVote(p) ==
    /\ alive[p]
    /\ final[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ final' = [final EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, sentVote, requestSent, recvVote,
                    decision, broadcastSent, coordAlive >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ final[p] = undecided
    /\ ~coordAlive
    /\ ~requestSent[p]         \* coordinator never sent request
    /\ final' = [final EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, sentVote, requestSent, recvVote,
                    decision, broadcastSent, coordAlive >>

DecideFromBroadcast(p) ==
    /\ alive[p]
    /\ final[p] = undecided
    /\ broadcastSent[p] \in {commit, abort}
    /\ final' = [final EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED << vote, alive, sentVote, requestSent, recvVote,
                    decision, broadcastSent, coordAlive >>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << vote, final, sentVote, requestSent, recvVote,
                    decision, broadcastSent, coordAlive >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Fairness assumptions (weak fairness on all progress actions except deaths)
\* ----------------------------------------------------------------------
Fairness ==
    /\ WF_vars(\E p \in participants: SendRequest(p))
    /\ WF_vars(\E p \in participants: ReceiveVote(p))
    /\ WF_vars(\E p \in participants: DetectFault(p))
    /\ WF_vars(MakeDecision)
    /\ WF_vars(\E p \in participants: Broadcast(p))
    /\ WF_vars(\E p \in participants: SendVote(p))
    /\ WF_vars(\E p \in participants: AbortOnVote(p))
    /\ WF_vars(\E p \in participants: AbortOnTimeout(p))
    /\ WF_vars(\E p \in participants: DecideFromBroadcast(p))

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ Fairness

\* ----------------------------------------------------------------------
\* Invariant (type correctness)
\* ----------------------------------------------------------------------
THEOREM TypeInvIsInvariant == Spec => []TypeInv

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
\* The configuration file expects the following names:
\*   Spec, Init, Next, TypeInv
\*   plus the constants declared above.
\* No additional top-level definitions are required.
====