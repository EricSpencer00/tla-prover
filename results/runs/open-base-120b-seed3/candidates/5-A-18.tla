---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    coordAlive, coordFaulty, coordDecision, 
    coordRequested, votesReceived, broadcastSent,
    participantAlive, participantFaulty, participantVote,
    participantSentVote, participantDecision

vars == << coordAlive, coordFaulty, coordDecision,
           coordRequested, votesReceived, broadcastSent,
           participantAlive, participantFaulty, participantVote,
           participantSentVote, participantDecision >>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInv ==
    /\ participants # {}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ votesReceived \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {commit, abort, notsent}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantSentVote \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantSentVote = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ votesReceived = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Coordinator actions
SendVoteReq(p) ==
    /\ coordAlive
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votesReceived, broadcastSent,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote,
                    participantDecision >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ votesReceived[p] = waiting
    /\ participantAlive[p]
    /\ participantSentVote[p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = participantVote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, broadcastSent,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote,
                    participantDecision >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ votesReceived[p] = waiting
    /\ ~participantAlive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty,
                    coordRequested, votesReceived, broadcastSent,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote,
                    participantDecision >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: votesReceived[p] # waiting
    /\ IF \A p \in participants: votesReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty,
                    coordRequested, votesReceived, broadcastSent,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote,
                    participantDecision >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, votesReceived,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote,
                    participantDecision >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordRequested, votesReceived,
                    broadcastSent,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote,
                    participantDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
SendVote(p) ==
    /\ participantAlive[p]
    /\ coordRequested[p]
    /\ ~participantSentVote[p]
    /\ participantSentVote' = [participantSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, votesReceived, broadcastSent,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision >>

AbortOnVote(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ participantSentVote[p]
    /\ participantVote[p] = no
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, votesReceived, broadcastSent,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote >>

AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ ~coordRequested[p]
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, votesReceived, broadcastSent,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote >>

DecideFromBroadcast(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, votesReceived,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote,
                    broadcastSent >>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, votesReceived, broadcastSent,
                    participantVote, participantSentVote,
                    participantDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ MakeDecision

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant
Invariant == TypeInv

\* ----------------------------------------------------------------------
\* Properties (safety)
AC1 == \A p,q \in participants :
          ~(participantDecision[p] = commit /\ participantDecision[q] = abort)

AC2 == \A p \in participants :
          participantDecision[p] = commit => 
            \A q \in participants : participantVote[q] = yes

AC3 == \A p \in participants :
          participantDecision[p] = abort =>
            \E q \in participants : participantVote[q] = no
            \/ \E q \in participants : ~participantAlive[q]
            \/ ~coordAlive

AC4 == \A p \in participants :
          \A d1,d2 \in {commit, abort} :
            (participantDecision[p] = d1 /\ participantDecision[p] = d2) => d1 = d2

\* ----------------------------------------------------------------------
\* Liveness (the blocking liveness component)
Liveness == <> ( \A p \in participants : participantDecision[p] # undecided )
             \/ <> (\E p \in participants : ~participantAlive[p])
             \/ <> ~coordAlive

====