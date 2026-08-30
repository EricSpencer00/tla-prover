---- MODULE ACP_SB ----
EXTENDS Integers, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Simple broadcast: the coordinator sends vote results one participant at a time.
\* If it dies mid-broadcast, some participants are left with no decision -- a blocking
\* outcome, which is why the non-blocking liveness property is NOT satisfied here.

VARIABLES partVote, partAlive, partDecision, partFaulty, partSent, coordRequested,
          coordRecv, coordBroadcasted, coordDecision, coordAlive, coordFaulty

vars == << partVote, partAlive, partDecision, partFaulty, partSent,
            coordRequested, coordRecv, coordBroadcasted, coordDecision,
            coordAlive, coordFaulty >>

TypeInv ==
    /\ partVote \in [participants -> {yes, no}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> {undecided, commit, abort}]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partSent \in [participants -> BOOLEAN]
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordBroadcasted \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ partVote \in [participants -> {yes, no}]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partDecision = [p \in participants |-> undecided]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partSent = [p \in participants |-> FALSE]
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordBroadcasted = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

CoordSendReq(p) ==
    /\ coordAlive
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSent,
                    coordRecv, coordBroadcasted, coordDecision, coordAlive, coordFaulty >>

\* The coordinator receives a vote only after the participant actually sent it.
CoordReceive(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordRecv[p] = waiting
    /\ partSent[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSent,
                    coordRequested, coordBroadcasted, coordDecision, coordAlive, coordFaulty >>

CoordDetectParticipantFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordRecv[p] = waiting
    /\ ~partAlive[p]
    /\ ~partSent[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSent,
                    coordRequested, coordRecv, coordBroadcasted, coordAlive, coordFaulty >>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordRequested[p]
    /\ \A p \in participants : coordRecv[p] # waiting
    /\ coordDecision' = IF (\A p \in participants : coordRecv[p] = yes) THEN commit ELSE abort
    /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSent,
                    coordRequested, coordRecv, coordBroadcasted, coordAlive, coordFaulty >>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcasted[p] = notsent
    /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSent,
                    coordRequested, coordRecv, coordDecision, coordAlive, coordFaulty >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSent,
                    coordRequested, coordRecv, coordBroadcasted, coordDecision >>

PartSendVote(p) ==
    /\ partAlive[p]
    /\ coordRequested[p]
    /\ ~partSent[p]
    /\ partSent' = [partSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty,
                    coordRequested, coordRecv, coordBroadcasted, coordDecision, coordAlive, coordFaulty >>

\* A no vote lets a participant unilaterally abort, bypassing the coordinator.
PartAbortOnVote(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ partSent[p]
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << partVote, partAlive, partFaulty, partSent,
                    coordRequested, coordRecv, coordBroadcasted, coordDecision, coordAlive, coordFaulty >>

PartAbortOnTimeout(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ ~coordAlive
    /\ ~coordRequested[p]
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << partVote, partAlive, partFaulty, partSent,
                    coordRequested, coordRecv, coordBroadcasted, coordDecision, coordAlive, coordFaulty >>

PartDecide(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ coordBroadcasted[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordBroadcasted[p]]
    /\ UNCHANGED << partVote, partAlive, partFaulty, partSent,
                    coordRequested, coordRecv, coordBroadcasted, coordDecision, coordAlive, coordFaulty >>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << partVote, partDecision, partSent,
                    coordRequested, coordRecv, coordBroadcasted, coordDecision, coordAlive, coordFaulty >>

CoordProgress == CoordMakeDecision \/ (\E p \in participants : CoordBroadcast(p))
PartProgress == (\E p \in participants : PartDecide(p)

Next ==
    \/ (\E p \in participants : CoordSendReq(p))
    \/ (\E p \in participants : CoordReceive(p))
    \/ (\E p \in participants : CoordDetectParticipantFault(p))
    \/ CoordMakeDecision
    \/ (\E p \in participants : CoordBroadcast(p))
    \/ CoordDie
    \/ (\E p \in participants : PartSendVote(p))
    \/ (\E p \in participants : PartAbortOnVote(p))
    \/ (\E p \in participants : PartAbortOnTimeout(p))
    \/ (\E p \in participants : PartDecide(p))
    \/ (\E p \in participants : PartDie(p))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordProgress)
    /\ WF_vars(PartProgress)

\* No two participants ever decide differently.
Agreement ==
    \A p, q \in participants :
        ~(partDecision[p] = commit /\ partDecision[q] = abort)

\* A commit requires unanimity.
CommitValidity == \A p \in participants : partDecision[p] = commit => \A q \in participants : partVote[q] = yes

\* An abort is justified by a no vote or a crash somewhere.
AbortValidity ==
    \A p \in participants :
        partDecision[p] = abort =>
            (\E q \in participants : partVote[q] = no) \/ (\E q \in participants : partFaulty[q]) \/ coordFaulty

\* Each participant decides at most once, and never re-decides.
Irrevocability ==
    \A p \in participants :
        (partDecision[p] = commit => (partDecision' [p] = commit))
        /\ (partDecision[p] = abort => (partDecision' [p] = abort))

EventualResolution ==
    <>(\A p \in participants : partDecision[p] # undecided \/ coordFaulty \/ (\E q \in participants : partFaulty[q]))

====