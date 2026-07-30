---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ broadcasted \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendReq(p) ==
    /\ coordAlive
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : reqSent[q]
    /\ recvVote[p] = waiting
    /\ sentVote[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, broadcasted, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : reqSent[q]
    /\ recvVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : recvVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted, coordAlive, coordFaulty>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

SendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqSent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~reqSent[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : RecvVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))
    /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
    /\ WF_vars(\E p \in participants : SendReq(p))
    /\ WF_vars(\E p \in participants : RecvVote(p))
    /\ WF_vars(\E p \in participants : Broadcast(p))
    /\ WF_vars(MakeDecision)

AC1 ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

AC2 ==
    \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AC3 ==
    \A p \in participants : decision[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faulty[q]
        \/ coordFaulty

AC4 ==
    \A p \in participants :
        /\ decision[p] = commit => (decision[p] = commit)
        /\ decision[p] = abort => (decision[p] = abort)

AC3Liveness ==
    <>(\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

====