---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Model of the Atomic Commitment Protocol with Simple Broadcast (ACP-SB).
\* Both the coordinator and participants can crash silently, and the
\* coordinator's decision is sent by simple (not quorum) broadcast, which
\* is why a coordinator crash during broadcast can leave participants
\* undecided -- the protocol is blocking, not non-blocking, under failure.
\* The invariants here are all safety properties; there is no liveness
\* guarantee that every non-faulty participant eventually decides.

VARIABLES vote, aliveP, decisionP, faultyP, sentVote,
         sentReq, recvVote, sentOut, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, sentVote,
          sentReq, recvVote, sentOut, decisionC, aliveC, faultyC>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ decisionP \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ sentReq \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {waiting, yes, no}]
  /\ sentOut \in [participants -> {notsent, commit, abort}]
  /\ decisionC \in {undecided, commit, abort}
  /\ aliveC \in BOOLEAN
  /\ faultyC \in BOOLEAN

Init ==
  /\ \E v \in [participants -> {yes, no}]:
       vote = v
  /\ aliveP = [p \in participants |-> TRUE]
  /\ decisionP = [p \in participants |-> undecided]
  /\ faultyP = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ sentReq = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ sentOut = [p \in participants |-> notsent]
  /\ decisionC = undecided
  /\ aliveC = TRUE
  /\ faultyC = FALSE

\* Coordinator actions:
\* 1. Send a vote request to a participant.
ReqVote(p) ==
  /\ aliveC
  /\ ~sentReq[p]
  /\ sentReq' = [sentReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 recvVote, sentOut, decisionC, aliveC, faultyC>>

\* 2. Receive a vote from a participant.
ReceiveVote(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A q \in participants: sentReq[q]
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, sentOut, decisionC, aliveC, faultyC>>

\* 3. Detect a participant fault and decide abort (at most one abort).
DetectFault(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A q \in participants: sentReq[q]
  /\ recvVote[p] = waiting
  /\ ~aliveP[p]
  /\ ~sentVote[p]
  /\ decisionC' = abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, recvVote, sentOut, aliveC, faultyC>>

\* 4. Make a commit/abort decision once all votes have arrived.
Decide ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A p \in participants: recvVote[p] # waiting
  /\ decisionC' = IF \A p \in participants: recvVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, recvVote, sentOut, aliveC, faultyC>>

\* 5. Broadcast the decision to a participant (simple broadcast).
Broadcast(p) ==
  /\ aliveC
  /\ decisionC # undecided
  /\ sentOut[p] = notsent
  /\ sentOut' = [sentOut EXCEPT ![p] = decisionC]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, recvVote, decisionC, aliveC, faultyC>>

\* 6. Die silently (no fairness guarantee on this).
DieC ==
  /\ aliveC
  /\ aliveC' = FALSE
  /\ faultyC' = TRUE
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                 sentReq, recvVote, sentOut, decisionC, aliveC, faultyC>>

\* Participant actions:
\* 1. Send vote to the coordinator once a request is received.
SendVote(p) ==
  /\ aliveP[p]
  /\ sentReq[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentReq,
                 recvVote, sentOut, decisionC, aliveC, faultyC>>

\* 2. Abort unilaterally once a no vote is cast.
AbortOnVote(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                 sentReq, recvVote, sentOut, decisionC, aliveC, faultyC>>

\* 3. Abort on timeout if the coordinator dies without asking.
AbortOnTimeout(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ ~aliveC
  /\ ~sentReq[p]
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                 sentReq, recvVote, sentOut, decisionC, aliveC, faultyC>>

\* 4. Adopt the coordinator's broadcast decision.
DecideFromC(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sentOut[p] # notsent
  /\ decisionP' = [decisionP EXCEPT ![p] = sentOut[p]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                 sentReq, recvVote, sentOut, decisionC, aliveC, faultyC>>

\* 5. Die silently (no fairness guarantee on this).
DieP(p) ==
  /\ aliveP[p]
  /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decisionP, sentVote, sentReq,
                 recvVote, sentOut, decisionC, aliveC, faultyC>>

\* Progress actions (all but the death actions; death actions have no fairness):
CoordProgress ==
  \E p \in participants:
    \/ ReqVote(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p)
    \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideFromC(p)
DecideStep == Decide
Next ==
  \/ CoordProgress
  \/ DecideStep
  \/ DieC
  \/ (\E p \in participants: DieP(p))

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CoordProgress) /\ WF_vars(DecideStep)

\* AC1: no two participants ever decide differently (commit vs abort).
Consistency ==
  \A p, q \in participants:
    (decisionP[p] = commit /\ decisionP[q] = abort) => FALSE

\* AC2: a commit can only happen when every participant voted yes.
CommitValidity ==
  (\E p \in participants: decisionP[p] = commit) =>
    (\A q \in participants: vote[q] = yes)

\* AC3: an abort can only happen if some participant voted no or some
\* actor has crashed -- an abort with unanimous yes and no crash is
\* disallowed. (The abort-on-commit-or-crash clause is the interesting
\* part; the abort-on-timeout clause is already covered by AbortOnVote
\* and DetectFault, but keeping it here makes the condition complete.)
AbortValidity ==
  (\E p \in participants: decisionP[p] = abort) =>
    (\E q \in participants: vote[q] = no) \/ (\E q \in participants: faultyP[q]) \/ faultyC

\* AC4: each participant's irreversible decision is one-way.
Irreversibility ==
  \A p \in participants:
    /\ (decisionP[p] = commit => (decisionP[p] = commit)@(1 ..))
    /\ (decisionP[p] = abort => (decisionP[p] = abort)@(1 ..))

TypeInv == TypeOK
====