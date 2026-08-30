---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES partVote, partAlive, partDecision, partFaulty, partSent
VARIABLES coordReqSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty

Vars == <<partVote, partAlive, partDecision, partFaulty, partSent,
           coordReqSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ partVote \in [participants -> {yes, no}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> {undecided, commit, abort}]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partSent \in [participants -> BOOLEAN]
    /\ coordReqSent \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {waiting, yes, no}]
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ partVote \in [participants -> {yes, no}]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partDecision = [p \in participants |-> undecided]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partSent = [p \in participants |-> FALSE]
    /\ coordReqSent = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator broadcasts decisions one participant at a time; a crash in the
\* middle is exactly what leaves some participants permanently undecided.
SendVoteReq(p) ==
    /\ coordAlive
    /\ ~coordReqSent[p]
    /\ coordReqSent' = [coordReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : coordReqSent[q]
    /\ coordRecv[p] = waiting
    /\ partSent[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordReqSent, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Failure detection is magical here: the coordinator "sees" the participant
\* die without any message exchange, which is what forces the abort decision.
DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : coordReqSent[q]
    /\ coordRecv[p] = waiting
    /\ ~partAlive[p]
    /\ ~partSent[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordReqSent, coordRecv, coordSent, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordRecv[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordReqSent, coordRecv, coordSent, coordAlive, coordFaulty>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordReqSent, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordReqSent, coordRecv, coordSent, coordDecision, coordFaulty>>

SendVote(p) ==
    /\ partAlive[p]
    /\ ~partSent[p]
    /\ coordReqSent[p]
    /\ partSent' = [partSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty,
                   coordReqSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ partSent[p]
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                   coordReqSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeoutForReq(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ ~coordReqSent[p]
    /\ ~coordAlive
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                   coordReqSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ coordSent[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                   coordReqSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<partVote, partDecision, partSent,
                   coordReqSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Progress only counts the actions that actually move the protocol towards a
\* decision; death itself is not assumed to happen "quickly".
Next ==
    \/ \E p \in participants :
         SendVoteReq(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p)
         \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeoutForReq(p)
         \/ DecideOnBroadcast(p) \/ PartDie(p)
    \/ MakeDecision
    \/ CoordDie

Spec ==
    /\ Init /\ [][Next]_Vars
    /\ WF_Vars(SendVoteReq(participants[1]))
    /\ WF_Vars(SendVoteReq(participants[2]))
    /\ WF_Vars(ReceiveVote(participants[1]))
    /\ WF_Vars(ReceiveVote(participants[2]))
    /\ WF_Vars(SendVote(participants[1]))
    /\ WF_Vars(SendVote(participants[2]))
    /\ WF_Vars(Broadcast(participants[1]))
    /\ WF_Vars(Broadcast(participants[2]))
    /\ WF_Vars(DecideOnBroadcast(participants[1]))
    /\ WF_Vars(DecideOnBroadcast(participants[2]))

\* Agreement: no two participants ever end up on different sides.
Agreement == \A p, q \in participants : ~(partDecision[p] = commit /\ partDecision[q] = abort)

\* A committed outcome is backed by a unanimous vote.
CommitValid == \A p \in participants : partDecision[p] = commit => \A q \in participants : partVote[q] = yes

\* An abort only happens if there really is a reason to.
AbortValid == \A p \in participants : partDecision[p] = abort =>
                  (\E q \in participants : partVote[q] = no) \/ (\E q \in participants : partFaulty[q]) \/ coordFaulty

\* A decision is final, once made.
DecideOnce == \A p \in participants : (partDecision[p] = commit) ~> (partDecision[p] = commit)
              /\ (partDecision[p] = abort) ~> (partDecision[p] = abort)

\* Termination, weakened: either everyone decides, or someone is found faulty.
EventualDecision == <>(\E p \in participants : partDecision[p] # undecided) \/ coordFaulty \/ (\E p \in participants : partFaulty[p])

====