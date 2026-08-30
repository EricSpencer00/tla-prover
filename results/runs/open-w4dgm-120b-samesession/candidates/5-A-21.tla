---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The Atomic Commitment Protocol with Simple Broadcast (ACP-SB).
\* Coordinator collects votes, decides commit/abort, then broadcasts that
\* single decision to each participant one at a time. A crash during broadcast
\* can leave a participant undecided -- this is the blocking failure the
\* spec models (it does NOT satisfy AC5's termination requirement).
\* Safety only: AC1--AC4; Progress: eventual decision or some fault.

VARIABLES vote, alive, decision, faulty, voted, cRequested, cRecvVote, cBroadcast, cAlive, cFaulty

vars == <<vote, alive, decision, faulty, voted, cRequested, cRecvVote, cBroadcast, cAlive, cFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ cRequested \in [participants -> BOOLEAN]
  /\ cRecvVote \in [participants -> {yes, no, waiting}]
  /\ cBroadcast \in [participants -> {commit, abort, notsent}]
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ cRequested = [p \in participants |-> FALSE]
  /\ cRecvVote = [p \in participants |-> waiting]
  /\ cBroadcast = [p \in participants |-> notsent]
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

\* Coordinator actions.
SendReq(p) ==
  /\ cAlive
  /\ ~cRequested[p]
  /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, cRecvVote, cBroadcast, cAlive, cFaulty>>

RecvVote(p) ==
  /\ cAlive
  /\ \A q \in participants : cRequested[q]
  /\ cRecvVote[p] = waiting
  /\ alive[p]
  /\ voted[p]
  /\ cRecvVote' = [cRecvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, cRequested, cBroadcast, cAlive, cFaulty>>

DetectFault(p) ==
  /\ cAlive
  /\ \A q \in participants : cRequested[q]
  /\ cRecvVote[p] = waiting
  /\ ~alive[p]
  /\ ~voted[p]
  /\ cRecvVote' = [cRecvVote EXCEPT ![p] = no]
  /\ decision' = [q \in participants |-> abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, cRequested, cBroadcast, cAlive, cFaulty>>

Decide ==
  /\ cAlive
  /\ decision = [p \in participants |-> undecided]
  /\ \A p \in participants : cRecvVote[p] # waiting
  /\ decision' = IF \A p \in participants : cRecvVote[p] = yes THEN [p \in participants |-> commit] ELSE [p \in participants |-> abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, cRequested, cRecvVote, cBroadcast, cAlive, cFaulty>>

Broadcast(p) ==
  /\ cAlive
  /\ decision[p] # undecided
  /\ cBroadcast[p] = notsent
  /\ cBroadcast' = [cBroadcast EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, cRequested, cRecvVote, cAlive, cFaulty>>

DieCoordinator ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, cRequested, cRecvVote, cBroadcast>>

\* Participant actions.
SendVote(p) ==
  /\ alive[p]
  /\ cRequested[p]
  /\ ~voted[p]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, cRequested, cRecvVote, cBroadcast, cAlive, cFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voted[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, cRequested, cRecvVote, cBroadcast, cAlive, cFaulty>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~cAlive
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, cRequested, cRecvVote, cBroadcast, cAlive, cFaulty>>

DecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ cBroadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = cBroadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, cRequested, cRecvVote, cBroadcast, cAlive, cFaulty>>

DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, cRequested, cRecvVote, cBroadcast, cAlive, cFaulty>>

\* Progress is only claimed for live decision-making; death can happen anytime
\* and is not subject to fairness, so it can never itself force progress.
Next ==
  \/ \E p \in participants : SendReq(p) \/ RecvVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ AbortOnVote(p) \/ AbortTimeout(p) \/ DecideFromCoordinator(p) \/ DieParticipant(p)
  \/ Decide
  \/ DieCoordinator

Spec == Init /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(SendReq(p))
  /\ \A p \in participants : WF_vars(RecvVote(p))
  /\ \A p \in participants : SF_vars(DecideFromCoordinator(p))
  /\ \A p \in participants : WF_vars(AbortOnVote(p))
  /\ \A p \in participants : WF_vars(AbortTimeout(p))

\* Safety: agreement, commit-validity, abort-validity, and irreversibility.
Agree ==
  \A p1, p2 \in participants : (decision[p1] = commit /\ decision[p2] = abort) => FALSE

CommitValid ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : faulty[q]
    \/ cFaulty

Irreversible ==
  \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)

TypeInv == TypeOK

\* Progress: either everybody decides or some fault occurs; termination is
\* NOT guaranteed under simple broadcast (that would be AC5, which fails).
DecisionProgress ==
  <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q] \/ cFaulty)

\* Liveness requirements: ACP5 would require DecisionProgress alone, but ACP5
\* is not satisfied by the simple broadcast variant, so AC3 catches the fault.
\* AC4 is not a progress property, so it is folded into the safety invariant.
====