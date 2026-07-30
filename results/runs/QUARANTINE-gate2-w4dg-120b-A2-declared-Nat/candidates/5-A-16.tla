---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faultyP, sentVote, requestSent, recvd, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faultyP, sentVote, requestSent, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

Init ==
  /\ \A p \in participants : vote[p] \in {yes, no}
  /\ \A p \in participants : alive[p] = TRUE
  /\ \A p \in participants : decision[p] = undecided
  /\ \A p \in participants : faultyP[p] = FALSE
  /\ \A p \in participants : sentVote[p] = FALSE
  /\ \A p \in participants : requestSent[p] = FALSE
  /\ \A p \in participants : recvd[p] = waiting
  /\ \A p \in participants : broadcasted[p] = notsent
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendRequest(p) ==
  /\ coordAlive
  /\ ~requestSent[p]
  /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faultyP, sentVote, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ requestSent[p]
  /\ recvd[p] = waiting
  /\ sentVote[p]
  /\ recvd' = [recvd EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faultyP, sentVote, requestSent, broadcasted, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ requestSent[p]
  /\ recvd[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faultyP, sentVote, requestSent, recvd, broadcasted, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : recvd[p] # waiting
  /\ coordDecision' = IF \A p \in participants : recvd[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faultyP, sentVote, requestSent, recvd, broadcasted, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcasted[p] = notsent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faultyP, sentVote, requestSent, recvd, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faultyP, sentVote, requestSent, recvd, broadcasted, coordDecision, coordFaulty>>

SendVote(p) ==
  /\ alive[p]
  /\ requestSent[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faultyP, requestSent, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

UnanimousAbort(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faultyP, sentVote, requestSent, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

TimeoutAbort(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~requestSent[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faultyP, sentVote, requestSent, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

DecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcasted[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<vote, alive, faultyP, sentVote, requestSent, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, requestSent, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendRequest(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : UnanimousAbort(p)
  \/ \E p \in participants : TimeoutAbort(p)
  \/ \E p \in participants : DecideFromCoordinator(p)
  \/ \E p \in participants : ParticipantDie(p)

CoordinatorFairness ==
  /\ WF_vars(\E p \in participants : SendRequest(p))
  /\ WF_vars(\E p \in participants : RecvVote(p))
  /\ WF_vars(MakeDecision)
  /\ WF_vars(\E p \in participants : BroadcastDecision(p))

ParticipantFairness ==
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : UnanimousAbort(p))
  /\ WF_vars(\E p \in participants : TimeoutAbort(p))
  /\ WF_vars(\E p \in participants : DecideFromCoordinator(p))

Spec == Init /\ Next /\ CoordinatorFairness /\ ParticipantFairness

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requestSent \in [participants -> BOOLEAN]
  /\ recvd \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Agreement ==
  \A p \in participants : decision[p] = commit => \A q \in participants : decision[q] = commit
  /\ \A p \in participants : decision[p] = abort => \A q \in participants : decision[q] = abort

CommitValidity ==
  \E p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \E p \in participants : decision[p] = abort =>
    (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faultyP[q]) \/ coordFaulty

Irrevocability ==
  \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)
  /\ \A p \in participants : (decision[p] = abort) ~> (decision[p] = abort)

DecisionEventuality ==
  <>(\A p \in participants : decision[p] # undecided \/ coordFaulty \/ \E q \in participants : faultyP[q])

====