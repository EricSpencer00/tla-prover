---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, reqSent, rcvd, sendDecision, gdecision

vars == <<vote, alive, decision, faulty, sentVote, reqSent, rcvd, sendDecision, gdecision>>

Init ==
    /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
    /\ alive = [p \in participants \cup {"coordinator"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {"coordinator"} |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ rcvd = [p \in participants |-> waiting]
    /\ sendDecision = [p \in participants |-> notsent]
    /\ gdecision = undecided

CoordSendRequest(p) ==
    /\ alive["coordinator"]
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, rcvd, sendDecision, gdecision>>

CoordReceiveVote(p) ==
    /\ alive["coordinator"]
    /\ gdecision = undecided
    /\ \A q \in participants: reqSent[q]
    /\ rcvd[p] = waiting
    /\ sentVote[p]
    /\ rcvd' = [rcvd EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, sendDecision, gdecision>>

CoordDetectFault(p) ==
    /\ alive["coordinator"]
    /\ gdecision = undecided
    /\ \A q \in participants: reqSent[q]
    /\ rcvd[p] = waiting
    /\ ~alive[p]
    /\ gdecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, rcvd, sendDecision>>

CoordMakeDecision ==
    /\ alive["coordinator"]
    /\ gdecision = undecided
    /\ \A p \in participants: rcvd[p] # waiting
    /\ gdecision' = IF \A p \in participants: rcvd[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, rcvd, sendDecision>>

CoordBroadcast(p) ==
    /\ alive["coordinator"]
    /\ gdecision # undecided
    /\ sendDecision[p] = notsent
    /\ sendDecision' = [sendDecision EXCEPT ![p] = gdecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, rcvd, gdecision>>

CoordDie ==
    /\ alive["coordinator"]
    /\ alive' = [alive EXCEPT !["coordinator"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["coordinator"] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent, rcvd, sendDecision, gdecision>>

PartSendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqSent, rcvd, sendDecision, gdecision>>

PartAbortOnNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, rcvd, sendDecision, gdecision>>

PartAbortOnNoRequest(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~reqSent[p]
    /\ ~alive["coordinator"]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, rcvd, sendDecision, gdecision>>

PartDecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sendDecision[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = sendDecision[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, rcvd, sendDecision, gdecision>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent, rcvd, sendDecision, gdecision>>

Next ==
    \/ \E p \in participants: CoordSendRequest(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ \E p \in participants: PartAbortOnNoRequest(p)
    \/ \E p \in participants: PartDecideFromCoordinator(p)
    \/ \E p \in participants: PartDie(p)

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coordinator"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coordinator"} -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ rcvd \in [participants -> {yes, no, waiting}]
    /\ sendDecision \in [participants -> {commit, abort, notsent}]
    /\ gdecision \in {undecided, commit, abort}

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants: PartSendVote(p))
    /\ WF_vars(\E p \in participants: PartAbortOnNo(p))
    /\ WF_vars(\E p \in participants: PartDecideFromCoordinator(p))
    /\ WF_vars(\E p \in participants: CoordMakeDecision)

Agree ==
    \A p, q \in participants: (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitIsUnanimous ==
    \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes

ValidAbort ==
    \E p \in participants: decision[p] = abort =>
        \/ \E q \in participants: vote[q] = no
        \/ \E q \in participants: faulty[q]
        \/ faulty["coordinator"]

DecideAtMostOnce ==
    \A p \in participants: (decision[p] = commit => (\A s \in [participants -> {undecided, commit, abort}]: s[p] = commit => s[p] = commit))
        /\ (decision[p] = abort => (\A s \in [participants -> {undecided, commit, abort}]: s[p] = abort => s[p] = abort))

EventualDecisionOrFailure ==
    <>(\A p \in participants: decision[p] # undecided \/ faulty[p] \/ faulty["coordinator"])

====