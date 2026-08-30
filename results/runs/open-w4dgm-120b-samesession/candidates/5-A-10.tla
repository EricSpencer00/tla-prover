---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordination messages travel either way: vote requests/replies (A2P), and
\* the coordinator's commit/abort broadcast (P2A). Both directions can stall
\* forever if the coordinator crashes mid-broadcast -- a blocking protocol.

VARIABLES vote, alive, decided, faulty, sentVote, requested, recvVote, broadcast, coordState

vars == <<vote, alive, decided, faulty, sentVote, requested, recvVote, broadcast, coordState>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decided \in [participants \cup {"coord"} -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requested \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ coordState \in {"alive", "crashed"}

Init ==
  /\ vote \in [p \in participants |-> CHOOSE x \in {yes, no} : TRUE]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decided = [p \in participants \cup {"coord"} |-> undecided]
  /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ requested = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordState = "alive"

\* A coordinator can only die while no decision has been sent to anyone.
DieCoordinator ==
  /\ coordState = "alive"
  /\ coordState' = "crashed"
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, sentVote, requested, recvVote, broadcast>>

SendVoteRequest(p) ==
  /\ coordState = "alive"
  /\ alive["coord"]
  /\ ~requested[p]
  /\ requested' = [requested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, recvVote, broadcast, coordState>>

SendVote(p) ==
  /\ alive[p]
  /\ requested[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, requested, recvVote, broadcast, coordState>>

\* The coordinator may wait forever for a vote -- that is exactly what the
\* blocking failure mode exists for, so there is no fairness assumption here.
ReceiveVote(p) ==
  /\ coordState = "alive"
  /\ alive["coord"]
  /\ decided["coord"] = undecided
  /\ requested[p]
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requested, broadcast, coordState>>

DetectFault(p) ==
  /\ coordState = "alive"
  /\ alive["coord"]
  /\ decided["coord"] = undecided
  /\ requested[p]
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ decided' = [decided EXCEPT !["coord"] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcast, coordState>>

MakeDecision ==
  /\ coordState = "alive"
  /\ alive["coord"]
  /\ decided["coord"] = undecided
  /\ \A p \in participants : requested[p] /\ recvVote[p] # waiting
  /\ decided' = [decided EXCEPT !["coord"] = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcast, coordState>>

BroadcastDecision(p) ==
  /\ coordState = "alive"
  /\ alive["coord"]
  /\ decided["coord"] # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = decided["coord"]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requested, recvVote, coordState>>

DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ broadcast[p] # notsent
  /\ decided' = [decided EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcast, coordState>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcast, coordState>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~alive["coord"]
  /\ ~requested[p]
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcast, coordState>>

DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, requested, recvVote, broadcast, coordState, sentVote>>

Unanimous == \A p \in participants : recvVote[p] = yes

CoordProgress ==
  \/ MakeDecision
  \/ DieCoordinator

ParticipantProgress(p) ==
  \/ SendVote(p)
  \/ AbortOnVote(p)
  \/ AbortOnTimeout(p)
  \/ DieParticipant(p)

Next ==
  \/ CoordProgress
  \/ \E p \in participants : ParticipantProgress(p)
  \/ \E p \in participants : SendVoteRequest(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ \E p \in participants : BroadcastDecision(p)
  \/ \E p \in participants : DecideFromBroadcast(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_Vars(CoordProgress)
  /\ \A p \in participants : SF_Vars(ParticipantProgress(p))

\* SAFETY: the result is a consistent cut on a fixed vote set.
Agreement ==
  \A p, q \in participants :
    (decided[p] = commit /\ decided[q] = abort) => FALSE

CommitValid ==
  \A p \in participants : decided[p] = commit => Unanimous

AbortValid ==
  \A p \in participants :
    decided[p] = abort =>
      \/ \E q \in participants : vote[q] = no
      \/ \E q \in participants : ~alive[q]
      \/ ~alive["coord"]

Irrevocability ==
  \A p \in participants :
    /\ (decided[p] = commit => decided' = [decided EXCEPT ![p] = commit])
    /\ (decided[p] = abort => decided' = [decided EXCEPT ![p] = abort])
    /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcast, coordState>>

Liveness ==
  \A p \in participants : <>(decided[p] # undecided \/ faulty[p] \/ ~alive["coord"])

\* The simple broadcast variant is blocking on a coordinator crash, so the
\* non-blocking termination property AC5 is omitted on purpose.
====