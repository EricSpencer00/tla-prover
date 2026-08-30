---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sendVote, reqsent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sendVote, reqsent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sendVote \in [participants -> BOOLEAN]
    /\ reqsent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {waiting, yes, no}]
    /\ broadcasted \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sendVote = [p \in participants |-> FALSE]
    /\ reqsent = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SentAll == \A p \in participants : reqsent[p]
ReceivedAll == \A p \in participants : recvVote[p] # waiting
AllYes == \A p \in participants : vote[p] = yes
SomeNo == \E p \in participants : vote[p] = no

\* Coordinator asks the participants to vote.
RequestVote(p) ==
    /\ coordAlive
    /\ ~reqsent[p]
    /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sendVote, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* The coordinator collects a vote a live participant has already sent.
CollectVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ SentAll
    /\ recvVote[p] = waiting
    /\ sendVote[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sendVote, reqsent, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* The coordinator notices a participant died before voting and decides to abort.
DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ SentAll
    /\ recvVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sendVote, reqsent, recvVote, broadcasted, coordAlive, coordFaulty>>

\* Having all votes, the coordinator decides commit or abort.
Decide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ ReceivedAll
    /\ coordDecision' = IF AllYes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sendVote, reqsent, recvVote, broadcasted, coordAlive, coordFaulty>>

\* Simple broadcast: the decision is sent to participants one at a time.
Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sendVote, reqsent, recvVote, coordDecision, coordAlive, coordFaulty>>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sendVote, reqsent, recvVote, broadcasted, coordDecision>>

\* A participant sends its pre-chosen vote to the coordinator.
SendVote(p) ==
    /\ alive[p]
    /\ ~sendVote[p]
    /\ reqsent[p]
    /\ sendVote' = [sendVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqsent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* A participant that voted no unilaterally aborts the transaction.
AbortOnNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sendVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sendVote, reqsent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* A participant times out waiting for the coordinator's vote request.
AbortOnNoReq(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~reqsent[p]
    /\ coordFaulty
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sendVote, reqsent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* A participant adopts the coordinator's broadcasted decision.
AdoptDecision(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, alive, faulty, sendVote, reqsent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sendVote, reqsent, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

CoordinatorProgress == Decide \/ CoordinatorDie

ParticipantProgress == \E p \in participants : SendVote(p) \/ AbortOnNo(p) \/ AbortOnNoReq(p) \/ AdoptDecision(p) \/ ParticipantDie(p)

Next ==
    \/ \E p \in participants : RequestVote(p)
    \/ \E p \in participants : CollectVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ CoordinatorProgress
    \/ \E p \in participants : Broadcast(p)
    \/ ParticipantProgress

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordinatorProgress)
    /\ SF_vars(ParticipantProgress)

\* Agreement: no two participants can decide differently.
DecisionAgreement ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid == \A p \in participants : decision[p] = commit => AllYes

AbortValid ==
    \A p \in participants :
        decision[p] = abort =>
            \/ SomeNo
            \/ \E q \in participants : faulty[q]
            \/ coordFaulty

DecideOnce ==
    \A p \in participants :
        /\ (decision[p] = commit => decision' [p] = commit)
        /\ (decision[p] = abort => decision' [p] = abort)

\* Non-blocking progress: either everyone decides or someone is faulty (the
\* simple broadcast variant does not guarantee everyone decides in the end).
EventualDecisionOrFault == <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q] \/ coordFaulty)

====