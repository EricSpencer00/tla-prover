---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decision, faultyP, sentVote, requested, recvVote, broadcast, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decision, faultyP, sentVote, requested, recvVote, broadcast, decisionC, aliveC, faultyC>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requested \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ decisionC \in {undecided, commit, abort}
  /\ aliveC \in BOOLEAN
  /\ faultyC \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faultyP = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ requested = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ decisionC = undecided
  /\ aliveC = TRUE
  /\ faultyC = FALSE

SendReq(p) ==
  /\ aliveC
  /\ ~requested[p]
  /\ requested' = [requested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sentVote, recvVote, broadcast, decisionC, aliveC, faultyC>>

ReceiveVote(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A q \in participants : requested[q]
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sentVote, requested, broadcast, decisionC, aliveC, faultyC>>

DetectFault(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A q \in participants : requested[q]
  /\ recvVote[p] = waiting
  /\ ~aliveP[p]
  /\ decisionC' = abort
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sentVote, requested, recvVote, broadcast, aliveC, faultyC>>

MakeDecision ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A p \in participants : recvVote[p] # waiting
  /\ decisionC' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sentVote, requested, recvVote, broadcast, aliveC, faultyC>>

BroadcastDecision(p) ==
  /\ aliveC
  /\ decisionC # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = decisionC]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sentVote, requested, recvVote, decisionC, aliveC, faultyC>>

DieC ==
  /\ aliveC
  /\ aliveC' = FALSE
  /\ faultyC' = TRUE
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sentVote, requested, recvVote, broadcast, decisionC, aliveC, faultyC>>

SendVote(p) ==
  /\ aliveP[p]
  /\ requested[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, requested, recvVote, broadcast, decisionC, aliveC, faultyC>>

AbortOnNo(p) ==
  /\ aliveP[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, requested, recvVote, broadcast, decisionC, aliveC, faultyC>>

AbortOnRequestTimeout(p) ==
  /\ aliveP[p]
  /\ decision[p] = undecided
  /\ ~requested[p]
  /\ ~aliveC
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, requested, recvVote, broadcast, decisionC, aliveC, faultyC>>

DecideOnBroadcast(p) ==
  /\ aliveP[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, requested, recvVote, broadcast, decisionC, aliveC, faultyC>>

DieP(p) ==
  /\ aliveP[p]
  /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, requested, recvVote, broadcast, decisionC, aliveC, faultyC>>

Next ==
  \/ \E p \in participants : SendReq(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)
  \/ DieC
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnNo(p)
  \/ \E p \in participants : AbortOnRequestTimeout(p)
  \/ \E p \in participants : DecideOnBroadcast(p)
  \/ \E p \in participants : DieP(p)

Spec == Init /\ [][Next]_vars

Agreement ==
  \A p, q \in participants : (decision[p] = commit) => (decision[q] = commit)

CommitValid ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
  \A p \in participants :
    decision[p] = abort =>
      \/ \E q \in participants : vote[q] = no
      \/ \E q \in participants : faultyP[q]
      \/ faultyC

Irreversible ==
  \A p \in participants :
    /\ (decision[p] = commit) ~> (decision[p] = commit)
    /\ (decision[p] = abort) ~> (decision[p] = abort)

Termination ==
  <>(\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faultyP[p]) \/ faultyC

====