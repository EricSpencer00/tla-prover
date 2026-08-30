---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

Broadcast == [participants -> {commit, abort, notsent}]

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordRequested, coordReceived, coordBroadcast,
          coordDecision, coordAlive, coordFaulty

vars == << participantVote, participantAlive, participantDecision, participantFaulty,
           participantSent, coordRequested, coordReceived, coordBroadcast,
           coordDecision, coordAlive, coordFaulty >>

TypeInv ==
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantSent \in [participants -> BOOLEAN]
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordReceived \in [participants -> {yes, no, waiting}]
    /\ coordBroadcast \in Broadcast
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

\* Simple broadcast, so the coordinator can "die midway" and leave some
\* participants undecided forever -- that is exactly what AC5 would forbids.
\* Here we name only the ranked safety properties (the AC5 shape is a liveness
\* shape, not a safety shape, and is deliberately left out of the spec below).
\* The coordinator's fault-detection transition is deliberately one-shot: it
\* fires on the first participant that both hasn't voted and has died.

Init ==
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantSent = [p \in participants |-> FALSE]
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ coordReceived = [p \in participants |-> waiting]
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendVoteRequest(p) ==
    /\ coordAlive
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                    participantFaulty, participantSent, coordReceived,
                    coordBroadcast, coordDecision, coordAlive, coordFaulty >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordReceived[p] = waiting
    /\ participantSent[p]
    /\ coordReceived' = [coordReceived EXCEPT ![p] = participantVote[p]]
    /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                    participantFaulty, participantSent, coordRequested,
                    coordBroadcast, coordDecision, coordAlive, coordFaulty >>

\* Most fatal of all: a timed-out vote request from a participant that has
\* already died. That is what stops the coordinator from waiting forever.
DetectParticipantFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordReceived[p] = waiting
    /\ ~participantAlive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                    participantFaulty, participantSent, coordRequested,
                    coordReceived, coordBroadcast, coordAlive, coordFaulty >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordReceived[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordReceived[p] = yes
                          THEN commit ELSE abort
    /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                    participantFaulty, participantSent, coordRequested,
                    coordReceived, coordBroadcast, coordAlive, coordFaulty >>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                    participantFaulty, participantSent, coordRequested,
                    coordReceived, coordDecision, coordAlive, coordFaulty >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                    participantFaulty, participantSent, coordRequested,
                    coordReceived, coordBroadcast, coordDecision >>

SendVote(p) ==
    /\ participantAlive[p]
    /\ coordRequested[p]
    /\ ~participantSent[p]
    /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                    participantFaulty, coordRequested, coordReceived,
                    coordBroadcast, coordDecision, coordAlive, coordFaulty >>

AbortOnVote(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ participantSent[p]
    /\ participantVote[p] = no
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                    participantSent, coordRequested, coordReceived,
                    coordBroadcast, coordDecision, coordAlive, coordFaulty >>

AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordRequested[p]
    /\ coordFaulty
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                    participantSent, coordRequested, coordReceived,
                    coordBroadcast, coordDecision, coordAlive, coordFaulty >>

DecideOnBroadcast(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                    participantSent, coordRequested, coordReceived,
                    coordBroadcast, coordDecision, coordAlive, coordFaulty >>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << participantVote, participantDecision, participantSent,
                    coordRequested, coordReceived, coordBroadcast, coordDecision,
                    coordAlive, coordFaulty >>

Next ==
    \/ MakeDecision
    \/ CoordDie
    \/ \E p \in participants :
           SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectParticipantFault(p)
           \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
           \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p) \/ ParticipantDie(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendVoteRequest("p1"))
    /\ WF_vars(ReceiveVote("p1"))
    /\ WF_vars(SendVote("p1"))
    /\ WF_vars(DecideOnBroadcast("p1"))

\* Safety: every participant that decided commit was unanimous.
AC1 ==
    \A p1, p2 \in participants :
        (participantDecision[p1] = commit /\ participantDecision[p2] = abort) => FALSE

AC2 ==
    \A p \in participants : participantDecision[p] = commit => participantVote[p] = yes

\* An abort is justified only by a dissenting vote or a failure (coordinator
\* or participant); the coordinator alone may never unilaterally abort.
AC3 ==
    \A p \in participants :
        (participantDecision[p] = abort) =>
            \/ \E q \in participants : participantVote[q] = no
             \/ \E q \in participants : participantFaulty[q]
             \/ coordFaulty

AC4 ==
    \A p \in participants :
        /\ (participantDecision[p] = commit) ~> (participantDecision[p] = commit)
        /\ (participantDecision[p] = abort) ~> (participantDecision[p] = abort)

\* The simple-broadcast shape is exactly what breaks the non-blocking claim:
\* a coordinator crash can freeze some participants forever.
AC5 ==
    <>(\A p \in participants : participantDecision[p] # undecided)

====