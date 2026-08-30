---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The simple broadcast here is a single shared counter per participant:
\* the coordinator broadcasts to each participant individually, and a
\* participant that is slow to receive its decision is not itself failed.

VARIABLES vote, alive, decision, faulty, sentVote,
          requested, recvVote, broadcasted, coordDecision

vars == <<vote, alive, decision, faulty, sentVote,
           requested, recvVote, broadcasted, coordDecision>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requested \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ requested = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ broadcasted = [p \in participants |-> notsent]
  /\ coordDecision = undecided

AllRequested == \A p \in participants : requested[p]
AllReceived == \A p \in participants : recvVote[p] # waiting
CoordDecided == coordDecision # undecided

CoordinatorAction == IF alive["coord"] THEN "alive" ELSE "dead"
ParticipantAction == IF \E p \in participants : alive[p] THEN "alive" ELSE "dead"

SendVoteRequest(p) ==
  /\ CoordinatorAction = "alive"
  /\ ~requested[p]
  /\ requested' = [requested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 recvVote, broadcasted, coordDecision>>

\* Receiving a vote is only possible once the participant has actually
\* sent its vote message, which is what models the asynchronous link.
ReceiveVote(p) ==
  /\ CoordinatorAction = "alive"
  /\ coordDecision = undecided
  /\ AllRequested
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 requested, broadcasted, coordDecision>>

DetectParticipantFault(p) ==
  /\ CoordinatorAction = "alive"
  /\ coordDecision = undecided
  /\ AllRequested
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 requested, recvVote, broadcasted>>

MakeDecision ==
  /\ CoordinatorAction = "alive"
  /\ coordDecision = undecided
  /\ AllRequested
  /\ AllReceived
  /\ coordDecision' = IF \A p \in participants : recvVote[p] = yes
                      THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 requested, recvVote, broadcasted>>

BroadcastDecision(p) ==
  /\ CoordinatorAction = "alive"
  /\ coordDecision # undecided
  /\ broadcasted[p] = notsent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 requested, recvVote, coordDecision>>

DieCoordinator ==
  /\ CoordinatorAction = "alive"
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ UNCHANGED <<vote, decision, sentVote, requested,
                 recvVote, broadcasted, coordDecision>>

SendVote(p) ==
  /\ alive[p]
  /\ requested[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty,
                 requested, recvVote, broadcasted, coordDecision>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 requested, recvVote, broadcasted, coordDecision>>

AbortNoVoteReq(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~requested[p]
  /\ ~alive["coord"]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 requested, recvVote, broadcasted, coordDecision>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcasted[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 requested, recvVote, broadcasted, coordDecision>>

DieParticipant(p) ==
  /\ alive[p]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, decision, sentVote, requested,
                 recvVote, broadcasted, coordDecision>>

CoordinatorStep == MakeDecision \/ DieCoordinator

ParticipantStep(p) ==
  \/ SendVote(p) \/ AbortOnVote(p) \/ AbortNoVoteReq(p)
  \/ DecideOnBroadcast(p) \/ DieParticipant(p)

Next ==
  \/ CoordinatorStep
  \/ \E p \in participants : CoordinatorStep \/ ParticipantStep(p)
  \/ \E p \in participants : SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectParticipantFault(p) \/ BroadcastDecision(p)

Spec == Init /\ [][Next]_vars
        /\ SF_vars(DecideOnBroadcast("p1"))
        /\ WF_vars(CoordinatorStep)
        /\ \A p \in participants : WF_vars(ParticipantStep(p))

TypeInv == TypeOK

\* No two participants can ever decide differently.
Agreement == \A p, q \in participants :
  (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid == \A p \in participants :
  decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid == \A p \in participants :
  decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : ~alive[q]
    \/ ~alive["coord"]

Irreversible == \A p \in participants :
  (decision[p] = commit => decision' [p] = commit) /\ (decision[p] = abort => decision' [p] = abort)

Terminate == \A p \in participants :
  (decision[p] = undecided) ~> (decision[p] # undecided)

====