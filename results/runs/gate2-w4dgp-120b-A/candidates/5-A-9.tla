---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, reqsent, recv, broadcast, cdecision

vars == <<vote, alive, decision, faulty, voted, reqsent, recv, broadcast, cdecision>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ reqsent \in [participants -> BOOLEAN]
  /\ recv \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ cdecision \in {undecided, commit, abort}

Init ==
  /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ reqsent = [p \in participants |-> FALSE]
  /\ recv = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ cdecision = undecided

CoordinatorSendRequest(p) ==
  /\ alive["coord"]
  /\ ~reqsent[p]
  /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, recv, broadcast, cdecision>>

CoordinatorReceiveVote(p) ==
  /\ alive["coord"]
  /\ cdecision = undecided
  /\ reqsent[p]
  /\ recv[p] = waiting
  /\ voted[p]
  /\ recv' = [recv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, reqsent, broadcast, cdecision>>

CoordinatorDetectFault(p) ==
  /\ alive["coord"]
  /\ cdecision = undecided
  /\ reqsent[p]
  /\ recv[p] = waiting
  /\ ~alive[p]
  /\ cdecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, reqsent, recv, broadcast>>

CoordinatorDecide ==
  /\ alive["coord"]
  /\ cdecision = undecided
  /\ \A p \in participants : recv[p] # waiting
  /\ cdecision' = IF \A p \in participants : recv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, reqsent, recv, broadcast>>

CoordinatorBroadcast(p) ==
  /\ alive["coord"]
  /\ cdecision # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = cdecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, reqsent, recv, cdecision>>

CoordinatorDie ==
  /\ alive["coord"]
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, reqsent, recv, broadcast, cdecision>>

ParticipantSendVote(p) ==
  /\ alive[p]
  /\ reqsent[p]
  /\ ~voted[p]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, reqsent, recv, broadcast, cdecision>>

ParticipantAbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voted[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, reqsent, recv, broadcast, cdecision>>

ParticipantAbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~alive["coord"]
  /\ ~reqsent[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, reqsent, recv, broadcast, cdecision>>

ParticipantDecide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, reqsent, recv, broadcast, cdecision>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, reqsent, recv, broadcast, cdecision>>

CoordinatorProgress ==
  \/ CoordinatorDecide
  \/ (\E p \in participants : CoordinatorSendRequest(p))

ParticipantProgress ==
  \/ (\E p \in participants : ParticipantSendVote(p))
  \/ (\E p \in participants : ParticipantDecide(p))

Next ==
  \/ CoordinatorProgress
  \/ ParticipantProgress
  \/ (\E p \in participants : CoordinatorReceiveVote(p))
  \/ (\E p \in participants : CoordinatorDetectFault(p))
  \/ (\E p \in participants : CoordinatorBroadcast(p))
  \/ (\E p \in participants : ParticipantAbortOnVote(p))
  \/ (\E p \in participants : ParticipantAbortOnTimeout(p))
  \/ (\E p \in participants : ParticipantDie(p))
  \/ CoordinatorDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordinatorProgress)
  /\ WF_vars(ParticipantProgress)

Agreement ==
  \A p \in participants, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : faulty[q]
    \/ faulty["coord"]

Irreversibility ==
  \A p \in participants :
    /\ (decision[p] = commit => decision[p] = commit)
    /\ (decision[p] = abort => decision[p] = abort)

EventualProgress ==
  <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ faulty["coord"])

====