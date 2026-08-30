---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision

vars == <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision>>

TypeOK ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ broadcasted \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}

Init ==
    /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
    /\ alive = [x \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [x \in participants \cup {"coord"} |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ coordDecision = undecided

SendRequest(p) ==
    /\ alive["coord"]
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, recvVote, broadcasted, coordDecision>>

ReceiveVote(p) ==
    /\ alive["coord"]
    /\ coordDecision = undecided
    /\ \A q \in participants : reqSent[q]
    /\ recvVote[p] = waiting
    /\ sentVote[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, broadcasted, coordDecision>>

DetectFault(p) ==
    /\ alive["coord"]
    /\ coordDecision = undecided
    /\ \A q \in participants : reqSent[q]
    /\ recvVote[p] = waiting
    /\ ~alive[p]
    /\ ~sentVote[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted>>

MakeDecision ==
    /\ alive["coord"]
    /\ coordDecision = undecided
    /\ \A p \in participants : recvVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, broadcasted>>

BroadcastDecision(p) ==
    /\ alive["coord"]
    /\ coordDecision # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, coordDecision>>

CoordDie ==
    /\ alive["coord"]
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent, recvVote, broadcasted, coordDecision>>

SendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqSent, recvVote, broadcasted, coordDecision>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~reqSent[p]
    /\ ~alive["coord"]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent, recvVote, broadcasted, coordDecision>>

Next ==
    \/ \E p \in participants : SendRequest(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars
    /\ \A p \in participants : SF_vars(Decide(p))
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : BroadcastDecision(p))

Agreement ==
    \A p, q \in participants :
        ~(decision[p] = commit /\ decision[q] = abort)

CommitValidity ==
    \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            \/ (\E q \in participants : vote[q] = no)
            \/ (\E q \in participants : ~alive[q])
            \/ ~alive["coord"]

Irrevocability ==
    \A p \in participants :
        /\ (decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
        /\ (decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])
        /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote, broadcasted, coordDecision>>

AC3Liveness ==
    <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ ~alive["coord"])

TypeInv == TypeOK

====