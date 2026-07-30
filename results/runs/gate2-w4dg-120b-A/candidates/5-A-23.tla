---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, requested, recvd, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, requested, recvd, broadcasted,
           coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requested \in [participants -> BOOLEAN]
  /\ recvd \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ requested = [p \in participants |-> FALSE]
  /\ recvd = [p \in participants |-> waiting]
  /\ broadcasted = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

RequestVote(p) ==
  /\ coordAlive
  /\ ~requested[p]
  /\ requested' = [requested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, recvd,
                 broadcasted, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : requested[q]
  /\ recvd[p] = waiting
  /\ sentVote[p]
  /\ recvd' = [recvd EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested,
                 broadcasted, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : requested[q]
  /\ recvd[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested,
                 recvd, broadcasted, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : recvd[p] # waiting
  /\ coordDecision' = IF \A p \in participants : recvd[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested,
                 recvd, broadcasted, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcasted[p] = notsent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested,
                 recvd, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested,
                 recvd, broadcasted, coordDecision>>

SendVote(p) ==
  /\ alive[p]
  /\ ~sentVote[p]
  /\ requested[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, requested,
                 recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested,
                 recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortNoReq(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~requested[p]
  /\ coordFaulty
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested,
                 recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcasted[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested,
                 recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, requested,
                 recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : RequestVote(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ \E p \in participants : Broadcast(p)
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortNoReq(p)
  \/ \E p \in participants : DecideFromBroadcast(p)
  \/ \E p \in participants : Die(p)
  \/ MakeDecision
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendVote("dummy")) /\ WF_vars(AbortOnVote("dummy"))
  /\ WF_vars(DecideFromBroadcast("dummy"))

Agreement ==
  ~(decision["dummy"] = commit /\ decision["dummy"] = abort)

CommitValidity ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : faulty[q]
    \/ coordFaulty

Irreversible ==
  \A p \in participants :
    /\ (decision[p] = commit => [decision EXCEPT ![p] = commit])
    /\ (decision[p] = abort => [decision EXCEPT ![p] = abort])

EventualDecisionOrFailure ==
  <>(\E p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

====