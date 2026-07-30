---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, requested, recvd, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, requested, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ requested \in [participants -> BOOLEAN]
    /\ recvd \in [participants -> {yes, no, waiting}]
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
    /\ requested = [p \in participants |-> FALSE]
    /\ recvd = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendReq(p) ==
    /\ coordAlive
    /\ ~requested[p]
    /\ requested' = [requested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants: requested[q]
    /\ recvd[p] = waiting
    /\ sentVote[p]
    /\ recvd' = [recvd EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, broadcasted, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants: requested[q]
    /\ recvd[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, recvd, broadcasted, coordAlive, coordFaulty>>

Decide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: recvd[p] # waiting
    /\ coordDecision' = IF \A p \in participants: recvd[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, recvd, broadcasted, coordAlive, coordFaulty>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, recvd, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, recvd, broadcasted, coordDecision, coordFaulty>>

SendVote(p) ==
    /\ alive[p]
    /\ requested[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, requested, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnReqTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~requested[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, requested, recvd, broadcasted, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: RecvVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ Decide
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnReqTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

Spec == Init /\ [][Next]_vars

Agree ==
    \A p, q \in participants: (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity == \E p \in participants: decision[p] = commit => (\A q \in participants: vote[q] = yes)

AbortValidity ==
    \E p \in participants: decision[p] = abort =>
        \/ \E q \in participants: vote[q] = no
        \/ \E q \in participants: faulty[q]
        \/ coordFaulty

Irrevocable ==
    \A p \in participants:
        /\ (decision[p] = commit => \A s \in participants: decision[s] = commit)
        /\ (decision[p] = abort => \A s \in participants: decision[s] = abort)

EventuallyDecideOrFail ==
    <>(\A p \in participants: decision[p] # undecided) \/ coordFaulty \/ (\E p \in participants: faulty[p])

====