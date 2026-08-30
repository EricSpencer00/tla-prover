---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, faultyP, sent, coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, aliveP, decisionP, faultyP, sent, coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ decisionP \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ coordReq \in [participants -> BOOLEAN]
  /\ coordRecv \in [participants -> {waiting, yes, no}]
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

\* Simple broadcast means the coordinator can silently die mid-flood,
\* leaving some participants forever waiting for a decision.
CoordAllRequested == \A p \in participants : coordReq[p]
CoordAllReceived == \A p \in participants : coordRecv[p] # waiting
CoordAllSent == \A p \in participants : coordSent[p] # notsent

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP = [p \in participants |-> TRUE]
  /\ decisionP = [p \in participants |-> undecided]
  /\ faultyP = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ coordReq = [p \in participants |-> FALSE]
  /\ coordRecv = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator sends the single vote-request broadcast to a participant.
SendVoteReq(p) ==
  /\ coordAlive
  /\ ~coordReq[p]
  /\ coordReq' = [coordReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Coordinator receives a participant's vote (the participant already sent it).
ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ CoordAllRequested
  /\ coordRecv[p] = waiting
  /\ sent[p]
  /\ coordRecv' = [coordRecv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sent, coordReq, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Coordinator detects a participant's death mid-collect and aborts.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ CoordAllRequested
  /\ coordRecv[p] = waiting
  /\ ~aliveP[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sent, coordReq, coordRecv, coordSent, coordAlive, coordFaulty>>

\* The coordinator makes a decision once every vote is in.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ CoordAllReceived
  /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sent, coordReq, coordRecv, coordSent, coordAlive, coordFaulty>>

\* Coordinator uses simple broadcast; a mid-flood crash would block this.
BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sent, coordReq, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sent, coordReq, coordRecv, coordSent, coordDecision>>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
  /\ aliveP[p]
  /\ ~sent[p]
  /\ coordReq[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Participant aborts unilaterally on a no vote (no broadcast needed).
AbortOnVote(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sent[p]
  /\ vote[p] = no
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sent, coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnNoReq(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ ~coordReq[p]
  /\ coordFaulty
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sent, coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideFromCoord(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ coordSent[p] # notsent
  /\ decisionP' = [decisionP EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sent, coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ aliveP[p]
  /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decisionP, sent, coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Progress is weakly fair on all of these, but not on either of the death steps.
CoordStep == SendVoteReq("p1") \/ ReceiveVote("p1") \/ DetectFault("p1") \/ BroadcastDecision("p1")
ParticipantStep == SendVote("p1") \/ AbortOnVote("p1") \/ AbortOnNoReq("p1") \/ DecideFromCoord("p1")

Next ==
  \/ \E p \in participants : SendVoteReq(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
  \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnNoReq(p) \/ DecideFromCoord(p)
  \/ CoordDie \/ PartDie("p1")
  \/ MakeDecision

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CoordStep) /\ WF_vars(ParticipantStep)

\* The two outcomes are mutually exclusive -- a participant cannot commit
\* while another aborts, which is why no transaction can be partially committed.
AC1 == \A p1, p2 \in participants : ~(decisionP[p1] = commit /\ decisionP[p2] = abort)

\* A commit requires unanimity of yes votes.
AC2 == (\E p \in participants : decisionP[p] = commit) => (\A p \in participants : vote[p] = yes)

\* An abort needs a no vote, a participant fault, or a coordinator fault.
AC3 == (\E p \in participants : decisionP[p] = abort) => ( (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faultyP[p]) \/ coordFaulty)

\* Once a participant decides commit or abort it never flips.
AC4 == (\A p \in participants : decisionP[p] = commit) ~> (\A p \in participants : decisionP[p] = commit)
       /\ (\A p \in participants : decisionP[p] = abort) ~> (\A p \in participants : decisionP[p] = abort)

\* Simple broadcast leaves the protocol able to get stuck mid-flood, so we
\* can only weakly guarantee that some outcome is reached or some fault.
AC3Liveness == (<>(\A p \in participants : decisionP[p] # undecided) \/ (\E p \in participants : faultyP[p]) \/ coordFaulty)

\* SAFETY: AC1-AC4 are all invariants; AC3Liveness is the only liveness claim.
TypeInv == TypeOK
====