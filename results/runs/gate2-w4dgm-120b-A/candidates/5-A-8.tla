---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent
\* ACP-SB: Atomic Commitment Protocol with Simple Broadcast (non-blocking
\* aborted under crash/failure, but not guaranteed to terminate).

VARIABLES vote, aliveP, decisionP, faultyP, sentVote
          , voted, coordDecision, aliveCoord, faultyCoord, sentDecision

vars == <<vote, aliveP, decisionP, faultyP, sentVote,
          voted, coordDecision, aliveCoord, faultyCoord, sentDecision>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ decisionP \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ voted \in [participants -> {waiting, yes, no}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ aliveCoord \in BOOLEAN
  /\ faultyCoord \in BOOLEAN
  /\ sentDecision \in [participants -> {notsent, commit, abort}]

Init ==
  /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
  /\ aliveP = [p \in participants |-> TRUE]
  /\ decisionP = [p \in participants |-> undecided]
  /\ faultyP = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> waiting]
  /\ coordDecision = undecided
  /\ aliveCoord = TRUE
  /\ faultyCoord = FALSE
  /\ sentDecision = [p \in participants |-> notsent]

\* Coordinator actions.
SendVoteReq(p) ==
  /\ aliveCoord
  /\ voted[p] = waiting
  /\ voted' = [voted EXCEPT ![p] = waiting]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, coordDecision, aliveCoord, faultyCoord, sentDecision>>

ReceiveVote(p) ==
  /\ aliveCoord
  /\ coordDecision = undecided
  /\ \A q \in participants : sentVote[q] = TRUE
  /\ voted[p] = waiting
  /\ sentVote[p] = TRUE
  /\ voted' = [voted EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, coordDecision, aliveCoord, faultyCoord, sentDecision>>

DetectParticipantFault(p) ==
  /\ aliveCoord
  /\ coordDecision = undecided
  /\ \A q \in participants : sentVote[q] = TRUE
  /\ voted[p] = waiting
  /\ aliveP[p] = FALSE
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 voted, aliveCoord, faultyCoord, sentDecision>>

MakeDecision ==
  /\ aliveCoord
  /\ coordDecision = undecided
  /\ \A p \in participants : sentVote[p] = TRUE
  /\ coordDecision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 voted, aliveCoord, faultyCoord, sentDecision>>

BroadcastDecision(p) ==
  /\ aliveCoord
  /\ coordDecision # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, voted, coordDecision, aliveCoord, faultyCoord>>

DieCoord ==
  /\ aliveCoord
  /\ aliveCoord' = FALSE
  /\ faultyCoord' = TRUE
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 voted, coordDecision, sentDecision>>

\* Participant actions.
SendVote(p) ==
  /\ aliveP[p]
  /\ sentVote[p] = FALSE
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voted,
                 coordDecision, aliveCoord, faultyCoord, sentDecision>>

AbortOnVote(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sentVote[p] = TRUE
  /\ vote[p] = no
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, voted, coordDecision,
                 aliveCoord, faultyCoord, sentDecision>>

AbortOnTimeout(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ aliveCoord = FALSE
  /\ sentVote[p] = FALSE
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, voted, coordDecision,
                 aliveCoord, faultyCoord, sentDecision>>

DecideFromBroadcast(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decisionP' = [decisionP EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, voted, coordDecision,
                 aliveCoord, faultyCoord, sentDecision>>

DieP(p) ==
  /\ aliveP[p]
  /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decisionP, sentVote, voted, coordDecision,
                 aliveCoord, faultyCoord, sentDecision>>

CoordStep == MakeDecision \/ DieCoord
ParticipantStep == \E p \in participants : SendVote(p) \/ AbortOnVote(p)
                    \/ AbortOnTimeout(p) \/ DecideFromBroadcast(p) \/ DieP(p)

Next ==
  \/ CoordStep \/ ParticipantStep
  \/ \E p \in participants :
       SendVoteReq(p) \/ ReceiveVote(p) \/ DetectParticipantFault(p)
       \/ BroadcastDecision(p)

\* Simple broadcast does NOT guarantee all participants decide; a crash during
\* broadcast can silently strand some participants.
DecideSome == \E p \in participants : decisionP[p] # undecided

Spec == Init /\ [][Next]_vars
        /\ SF_Vars(CoordStep) /\ SF_Vars(ParticipantStep)
        /\ WF_Vars(DecideSome)

TypeInv == TypeOK

\* Safety: no two participants ever decide differently, and unanimity of
\* commit holds exactly: a commit decision can only arise from all-yes votes.
\* Crash-faults are what make an abort decision go either way.
Agreement ==
  /\ \A p, q \in participants : (decisionP[p] = commit) => (decisionP[q] # abort)
  /\ ( (\E p \in participants : decisionP[p] = commit) =>
        \A p \in participants : vote[p] = yes )
  /\ ( (\E p \in participants : decisionP[p] = abort) =>
        (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faultyP[p]) \/ faultyCoord )
  /\ \A p \in participants :
       (decisionP[p] = commit => decisionP' [p] = commit)
       /\ (decisionP[p] = abort => decisionP' [p] = abort)

Termination ==
  <>( \A p \in participants : decisionP[p] # undecided \/ faultyCoord )

====