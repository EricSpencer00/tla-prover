---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Vote choice a participant has recorded.
Choice == {yes, no}

VARIABLES vote, aliveP, decisionP, faultyP, sentVote, reqSent,
           recvVote, broadcast, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, sentVote, reqSent,
           recvVote, broadcast, decisionC, aliveC, faultyC>>

\* A participant may crash silently (crash-stop, stop sending or deciding).
Dead(v) == ~aliveP[v]

Init ==
  /\ vote \in [participants -> Choice]
  /\ \A v \in participants : decisionP[v] = undecided
  /\ aliveP = [v \in participants |-> TRUE]
  /\ faultyP = [v \in participants |-> FALSE]
  /\ sentVote = [v \in participants |-> FALSE]
  /\ reqSent = [v \in participants |-> FALSE]
  /\ recvVote = [v \in participants |-> waiting]
  /\ broadcast = [v \in participants |-> notsent]
  /\ decisionC = undecided
  /\ aliveC = TRUE
  /\ faultyC = FALSE

\* Coordinator sends a vote request to a participant.
SendReq(v) ==
  /\ aliveC
  /\ ~reqSent[v]
  /\ reqSent' = [reqSent EXCEPT ![v] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, recvVote,
                 broadcast, decisionC, aliveC, faultyC>>

\* Coordinator receives a vote from a participant.
RecvVote(v) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ reqSent[v]
  /\ recvVote[v] = waiting
  /\ sentVote[v]
  /\ recvVote' = [recvVote EXCEPT ![v] = vote[v]]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, reqSent,
                 broadcast, decisionC, aliveC, faultyC>>

\* Coordinator detects a participant's silent failure and decides abort.
DecideAbortOnFault(v) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ reqSent[v]
  /\ recvVote[v] = waiting
  /\ Dead(v)
  /\ decisionC' = abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, reqSent,
                 recvVote, broadcast, aliveC, faultyC>>

AllVotesRecvd == \A v \in participants : recvVote[v] # waiting

DecideAbortOnVote(v) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ reqSent[v]
  /\ recvVote[v] = no
  /\ decisionC' = abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, reqSent,
                 recvVote, broadcast, aliveC, faultyC>>

\* Coordinator decides (commit iff every vote is yes, abort otherwise).
Decide ==
  /\ aliveC
  /\ decisionC = undecided
  /\ AllVotesRecvd
  /\ decisionC' = IF \A v \in participants : recvVote[v] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, reqSent,
                 recvVote, broadcast, aliveC, faultyC>>

\* Coordinator broadcasts its decision to a participant (simple sequential broadcast).
Broadcast(v) ==
  /\ aliveC
  /\ decisionC # undecided
  /\ broadcast[v] = notsent
  /\ broadcast' = [broadcast EXCEPT ![v] = decisionC]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, reqSent,
                 recvVote, decisionC, aliveC, faultyC>>

\* Participant crashes silently.
DieP(v) ==
  /\ aliveP[v]
  /\ aliveP' = [aliveP EXCEPT ![v] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![v] = TRUE]
  /\ UNCHANGED <<vote, decisionP, sentVote, reqSent,
                 recvVote, broadcast, decisionC, aliveC, faultyC>>

\* Coordinator crashes silently.
DieC ==
  /\ aliveC
  /\ aliveC' = FALSE
  /\ faultyC' = TRUE
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote, reqSent,
                 recvVote, broadcast, decisionC, faultyC>>

\* Participant sends its vote to the coordinator.
SendVote(v) ==
  /\ aliveP[v]
  /\ reqSent[v]
  /\ ~sentVote[v]
  /\ sentVote' = [sentVote EXCEPT ![v] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, reqSent,
                 recvVote, broadcast, decisionC, aliveC, faultyC>>

\* Participant aborts upon seeing its own vote is no.
AbortOnVote(v) ==
  /\ aliveP[v]
  /\ decisionP[v] = undecided
  /\ sentVote[v]
  /\ vote[v] = no
  /\ decisionP' = [decisionP EXCEPT ![v] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, reqSent,
                 recvVote, broadcast, decisionC, aliveC, faultyC>>

\* Participant aborts if the coordinator died without requesting its vote.
AbortOnTimeout(v) ==
  /\ aliveP[v]
  /\ decisionP[v] = undecided
  /\ ~reqSent[v]
  /\ faultyC
  /\ decisionP' = [decisionP EXCEPT ![v] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, reqSent,
                 recvVote, broadcast, decisionC, aliveC, faultyC>>

\* Participant adopts the coordinator's broadcast decision.
DecideOnBroadcast(v) ==
  /\ aliveP[v]
  /\ decisionP[v] = undecided
  /\ broadcast[v] # notsent
  /\ decisionP' = [decisionP EXCEPT ![v] = broadcast[v]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, reqSent,
                 recvVote, broadcast, decisionC, aliveC, faultyC>>

Next ==
  \/ \E v \in participants : SendReq(v)
  \/ \E v \in participants : RecvVote(v)
  \/ \E v \in participants : DecideAbortOnFault(v)
  \/ \E v \in participants : DecideAbortOnVote(v)
  \/ Decide
  \/ \E v \in participants : Broadcast(v)
  \/ DieC
  \/ \E v \in participants : DieP(v)
  \/ \E v \in participants : SendVote(v)
  \/ \E v \in participants : AbortOnVote(v)
  \/ \E v \in participants : AbortOnTimeout(v)
  \/ \E v \in participants : DecideOnBroadcast(v)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A v \in participants : WF_vars(SendReq(v))
  /\ \A v \in participants : WF_vars(SendVote(v))
  /\ \A v \in participants : WF_vars(DecideOnBroadcast(v))

TypeInv ==
  /\ vote \in [participants -> Choice]
  /\ decisionP \in [participants -> {undecided, commit, abort}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ reqSent \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {waiting} \cup Choice]
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ decisionC \in {undecided, commit, abort}
  /\ aliveC \in BOOLEAN
  /\ faultyC \in BOOLEAN

\* Safety: no two participants ever decide differently.
AgreementConsistent == \A v1, v2 \in participants : decisionP[v1] # undecided => decisionP[v1] = decisionP[v2]

\* Safety: a commit is backed by unanimous yes.
ValidCommit == \A v \in participants : decisionP[v] = commit => \A w \in participants : vote[w] = yes

\* Safety: an abort is justified by a no vote or a failure.
ValidAbort == \A v \in participants : decisionP[v] = abort =>
                 (\E w \in participants : vote[w] = no) \/ (\E w \in participants : faultyP[w]) \/ faultyC

\* Safety: a participant decides at most once (commit and abort are exclusive).
DecideAtMostOnce ==
  \A v \in participants :
    /\ (decisionP[v] = commit => decisionP' = [decisionP EXCEPT ![v] = commit])
    /\ (decisionP[v] = abort => decisionP' = [decisionP EXCEPT ![v] = abort])

\* Liveness: either all participants decide, or some failure occurs.
Termination == <>(\A v \in participants : decisionP[v] # undecided \/ faultyP[v] \/ faultyC)

====