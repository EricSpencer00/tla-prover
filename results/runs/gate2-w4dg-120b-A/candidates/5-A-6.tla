---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, faultyP, sentVote,
         sentReq, voteRecv, sentCoord, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, sentVote,
          sentReq, voteRecv, sentCoord, decisionC, aliveC, faultyC>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ decisionP \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ sentReq \in [participants -> BOOLEAN]
  /\ voteRecv \in [participants -> {yes, no, waiting}]
  /\ sentCoord \in [participants -> {notsent, commit, abort}]
  /\ decisionC \in {undecided, commit, abort}
  /\ aliveC \in BOOLEAN
  /\ faultyC \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP = [p \in participants |-> TRUE]
  /\ decisionP = [p \in participants |-> undecided]
  /\ faultyP = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ sentReq = [p \in participants |-> FALSE]
  /\ voteRecv = [p \in participants |-> waiting]
  /\ sentCoord = [p \in participants |-> notsent]
  /\ decisionC = undecided
  /\ aliveC = TRUE
  /\ faultyC = FALSE

SendRequest(p) ==
  /\ aliveC
  /\ ~sentReq[p]
  /\ sentReq' = [sentReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 voteRecv, sentCoord, decisionC, aliveC, faultyC>>

ReceiveVote(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A q \in participants: sentReq[q]
  /\ voteRecv[p] = waiting
  /\ sentVote[p]
  /\ voteRecv' = [voteRecv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, sentCoord, decisionC, aliveC, faultyC>>

CoordDetectFault(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A q \in participants: sentReq[q]
  /\ voteRecv[p] = waiting
  /\ ~aliveP[p]
  /\ decisionC' = abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, voteRecv, sentCoord, aliveC, faultyC>>

MakeDecision ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A q \in participants: voteRecv[q] # waiting
  /\ decisionC' = IF \A q \in participants: voteRecv[q] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, voteRecv, sentCoord, aliveC, faultyC>>

BroadcastDecision(p) ==
  /\ aliveC
  /\ decisionC # undecided
  /\ sentCoord[p] = notsent
  /\ sentCoord' = [sentCoord EXCEPT ![p] = decisionC]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, voteRecv, decisionC, aliveC, faultyC>>

CoordDie ==
  /\ aliveC
  /\ aliveC' = FALSE
  /\ faultyC' = TRUE
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, voteRecv, sentCoord, decisionC, faultyC>>

SendVote(p) ==
  /\ aliveP[p]
  /\ sentReq[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP,
                 sentReq, voteRecv, sentCoord, decisionC, aliveC, faultyC>>

AbortOnVote(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                 sentReq, voteRecv, sentCoord, decisionC, aliveC, faultyC>>

AbortOnTimeout(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ ~sentReq[p]
  /\ ~aliveC
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                 sentReq, voteRecv, sentCoord, decisionC, aliveC, faultyC>>

DecideFromCoord(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sentCoord[p] # notsent
  /\ decisionP' = [decisionP EXCEPT ![p] = sentCoord[p]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                 sentReq, voteRecv, sentCoord, decisionC, aliveC, faultyC>>

PartDie(p) ==
  /\ aliveP[p]
  /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decisionP, sentVote,
                 sentReq, voteRecv, sentCoord, decisionC, aliveC, faultyC>>

Next ==
  \/ MakeDecision
  \/ CoordDie
  \/ \E p \in participants: SendRequest(p) \/ ReceiveVote(p) \/ CoordDetectFault(p)
  \/ \E p \in participants: BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p) \/ DecideFromCoord(p) \/ PartDie(p)

CoordProgress ==
  \/ MakeDecision
  \/ CoordDie
  \/ \E p \in participants: SendRequest(p) \/ ReceiveVote(p) \/ CoordDetectFault(p)
  \/ \E p \in participants: BroadcastDecision(p)

PartProgress ==
  \E p \in participants: SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
  \/ \E p \in participants: DecideFromCoord(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordProgress)
  /\ SF_vars(PartProgress)

NoDecisionDisagreement ==
  \A p \in participants: \A q \in participants:
    (decisionP[p] = commit /\ decisionP[q] = abort) => FALSE

CommitOnlyWithAllYes ==
  (\E p \in participants: decisionP[p] = commit) => (\A p \in participants: vote[p] = yes)

AbortOnlyWithNoVoteOrFault ==
  (\E p \in participants: decisionP[p] = abort) =>
    \/ (\E p \in participants: vote[p] = no)
    \/ (\E p \in participants: faultyP[p])
    \/ faultyC

IrreversibleDecision ==
  \A p \in participants: (decisionP[p] = commit) ~> (decisionP[p] = commit)
                         /\ (decisionP[p] = abort) ~> (decisionP[p] = abort)

EventuallyDecideOrFault ==
  (\A p \in participants: <>(decisionP[p] # undecided))
    \/ (\E p \in participants: <>(faultyP[p]))
    \/ <>(faultyC)

====