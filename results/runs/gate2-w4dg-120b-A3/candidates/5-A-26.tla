---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentvote, coordReqd, coordRecv, coordSent, coordDecision, coordAlive

vars == <<vote, alive, decision, faulty, sentvote, coordReqd, coordRecv, coordSent, coordDecision, coordAlive>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ sentvote \in [participants -> BOOLEAN]
    /\ coordReqd \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
    /\ sentvote = [p \in participants |-> FALSE]
    /\ coordReqd = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE

SendVoteRequest(p) ==
    /\ coordAlive
    /\ ~coordReqd[p]
    /\ coordReqd' = [coordReqd EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordRecv, coordSent, coordDecision>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : coordReqd[q]
    /\ coordRecv[p] = waiting
    /\ sentvote[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReqd, coordSent, coordDecision, coordAlive>>

DetectParticipantFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : coordReqd[q]
    /\ coordRecv[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReqd, coordRecv, coordSent, coordAlive>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordRecv[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReqd, coordRecv, coordSent, coordAlive>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReqd, coordRecv, coordDecision, coordAlive>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED <<vote, decision, sentvote, coordReqd, coordRecv, coordSent, coordDecision>>

ParticipantSendVote(p) ==
    /\ alive[p]
    /\ coordReqd[p]
    /\ ~sentvote[p]
    /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordReqd, coordRecv, coordSent, coordDecision, coordAlive>>

ParticipantAbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentvote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentvote, coordReqd, coordRecv, coordSent, coordDecision, coordAlive>>

ParticipantAbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~coordReqd[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentvote, coordReqd, coordRecv, coordSent, coordDecision, coordAlive>>

AdoptCoordinatorDecision(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentvote, coordReqd, coordRecv, coordSent, coordDecision, coordAlive>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentvote, coordReqd, coordRecv, coordSent, coordDecision, coordAlive>>

Next ==
    \/ \E p \in participants : SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectParticipantFault(p) \/ BroadcastDecision(p) \/ ParticipantSendVote(p) \/ ParticipantAbortOnVote(p) \/ ParticipantAbortOnTimeout(p) \/ AdoptCoordinatorDecision(p) \/ ParticipantDie(p)
    \/ MakeDecision
    \/ CoordDie

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : ParticipantSendVote(p))
    /\ WF_vars(\E p \in participants : ParticipantAbortOnVote(p))
    /\ WF_vars(\E p \in participants : ParticipantAbortOnTimeout(p))
    /\ WF_vars(\E p \in participants : AdoptCoordinatorDecision(p))
    /\ WF_vars(MakeDecision)

AC1 == ~(\E p \in participants : decision[p] = commit /\ \E q \in participants : decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => (\E p \in participants : vote[p] = no \/ faulty[p] \/ faulty["coord"])
AC4 == (\A p \in participants : (decision[p] = commit) ~> (decision[p] = commit))
    /\ (\A p \in participants : (decision[p] = abort) ~> (decision[p] = abort))
AC5 == <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ faulty["coord"])

====