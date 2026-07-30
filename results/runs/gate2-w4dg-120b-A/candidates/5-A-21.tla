---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcastSent, cdecision

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {yes, no, notsent}]
    /\ cdecision \in {undecided, commit, abort}

Init ==
    /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ cdecision = undecided

SendReq(p) ==
    /\ alive["coord"]
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, recvVote, broadcastSent, cdecision>>

RecvVote(p) ==
    /\ alive["coord"]
    /\ cdecision = undecided
    /\ reqSent[p]
    /\ recvVote[p] = waiting
    /\ sentVote[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, broadcastSent, cdecision>>

DetectFault(p) ==
    /\ alive["coord"]
    /\ cdecision = undecided
    /\ reqSent[p]
    /\ recvVote[p] = waiting
    /\ ~alive[p]
    /\ cdecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcastSent>>

MakeDecision ==
    /\ alive["coord"]
    /\ cdecision = undecided
    /\ \A p \in participants : recvVote[p] # waiting
    /\ cdecision' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcastSent>>

Broadcast(p) ==
    /\ alive["coord"]
    /\ cdecision # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = cdecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, cdecision>>

CoordDie ==
    /\ alive["coord"]
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent, recvVote, broadcastSent, cdecision>>

SendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqSent, recvVote, broadcastSent, cdecision>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcastSent, cdecision>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~alive["coord"]
    /\ ~reqSent[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcastSent, cdecision>>

DecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcastSent, cdecision>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent, recvVote, broadcastSent, cdecision>>

Next ==
    \/ MakeDecision
    \/ CoordDie
    \/ \E p \in participants :
        \/ SendReq(p) \/ RecvVote(p) \/ DetectFault(p) \/ Broadcast(p)
        \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
        \/ DecideFromCoordinator(p) \/ PartDie(p)

Spec ==
    /\ Init
    /\ [][Next]_<<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcastSent, cdecision>>
    /\ WF_vars(SendVote("anyone"))
    /\ WF_vars(AbortOnVote("anyone"))
    /\ WF_vars(DecideFromCoordinator("anyone"))
    /\ WF_vars(SendReq("anyone"))
    /\ WF_vars(RecvVote("anyone"))
    /\ WF_vars(SendReq("anyone"))

AC1 == \A p1, p2 \in participants : ~ (decision[p1] = commit /\ decision[p2] = abort)
AC2 == \A p1, p2 \in participants : decision[p1] = commit => vote[p2] = yes
AC3 == \A p1, p2 \in participants : decision[p1] = abort => (vote[p2] = no \/ faulty[p2] \/ faulty["coord"])
AC4 == \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit) /\ (decision[p] = abort) ~> (decision[p] = abort)

Liveness ==
    <> (\A p \in participants : decision[p] # undecided \/ faulty[p] \/ faulty["coord"])

====