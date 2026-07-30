---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants \subseteq [id: 1..Cardinality(participants)]

VARIABLES vote, alive, decision, faulty, sentvote
VARIABLES reqsent, recvvote, broadcast, cdecision, calive

vars == <<vote, alive, decision, faulty, sentvote,
          reqsent, recvvote, broadcast, cdecision, calive>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentvote \in [participants -> BOOLEAN]
  /\ reqsent \in [participants -> BOOLEAN]
  /\ recvvote \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ cdecision \in {undecided, commit, abort}
  /\ calive \in BOOLEAN

Init ==
  /\ \E v \in [participants -> {yes, no}]: vote = v
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
  /\ sentvote = [p \in participants |-> FALSE]
  /\ reqsent = [p \in participants |-> FALSE]
  /\ recvvote = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ cdecision = undecided
  /\ calive = TRUE

CoordinatorSendReq(p) ==
  /\ calive
  /\ ~reqsent[p]
  /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote,
                recvvote, broadcast, cdecision, calive>>

CoordinatorRecvVote(p) ==
  /\ calive
  /\ cdecision = undecided
  /\ \A q \in participants: reqsent[q]
  /\ recvvote[p] = waiting
  /\ sentvote[p]
  /\ recvvote' = [recvvote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote,
                reqsent, broadcast, cdecision, calive>>

CoordinatorDetectFault(p) ==
  /\ calive
  /\ cdecision = undecided
  /\ \A q \in participants: reqsent[q]
  /\ recvvote[p] = waiting
  /\ ~alive[p]
  /\ cdecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote,
                reqsent, recvvote, broadcast, calive>>

CoordinatorMakeDecision ==
  /\ calive
  /\ cdecision = undecided
  /\ \A p \in participants: recvvote[p] # waiting
  /\ cdecision' = IF \A p \in participants: recvvote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote,
                reqsent, recvvote, broadcast, calive>>

CoordinatorBroadcast(p) ==
  /\ calive
  /\ cdecision # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = cdecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote,
                reqsent, recvvote, cdecision, calive>>

CoordinatorDie ==
  /\ calive
  /\ calive' = FALSE
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ UNCHANGED <<vote, decision, sentvote,
                reqsent, recvvote, broadcast, cdecision>>

ParticipantSendVote(p) ==
  /\ alive[p]
  /\ reqsent[p]
  /\ ~sentvote[p]
  /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty,
                reqsent, recvvote, broadcast, cdecision, calive>>

ParticipantAbortOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentvote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentvote,
                reqsent, recvvote, broadcast, cdecision, calive>>

ParticipantAbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~calive
  /\ ~reqsent[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentvote,
                reqsent, recvvote, broadcast, cdecision, calive>>

ParticipantDecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentvote,
                reqsent, recvvote, broadcast, cdecision, calive>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentvote,
                reqsent, recvvote, broadcast, cdecision, calive>>

Next ==
  \E p \in participants:
    \/ CoordinatorSendReq(p) \/ CoordinatorRecvVote(p) \/ CoordinatorDetectFault(p)
    \/ CoordinatorBroadcast(p) \/ ParticipantSendVote(p) \/ ParticipantAbortOnNo(p)
    \/ ParticipantAbortOnTimeout(p) \/ ParticipantDecideOnBroadcast(p)
    \/ ParticipantDie(p) \/ CoordinatorDie
  \/ CoordinatorMakeDecision

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ParticipantSendVote("a"))
        /\ WF_vars(ParticipantAbortOnNo("a"))
        /\ WF_vars(ParticipantAbortOnTimeout("a"))
        /\ WF_vars(ParticipantDecideOnBroadcast("a"))

AC1 == \A p, q \in participants:
         (decision[p] = commit /\ decision[q] = abort) => p = q

AC2 == \A p, q \in participants:
         (decision[p] = commit /\ vote[q] = no) => FALSE

AC3 == \A p, q \in participants:
         (decision[p] = abort /\ vote[q] = yes) => FALSE

AC4 == \A p \in participants:
         (decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
         /\ (decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])

EventuallyDecision ==
  <>(\E p \in participants: decision[p] # undecided) \/ (\E p \in participants \cup {"coord"}: faulty[p])

====