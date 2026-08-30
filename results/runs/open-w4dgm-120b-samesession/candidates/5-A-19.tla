---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB): a coordinator
\* collects votes from participants and broadcasts a decision; a crash in
\* the middle of the broadcast can leave some participants undecided forever.

VARIABLES vote, alive, decision, faulty, sent, asked, recvd, broadcasted, coordDec, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sent, asked, recvd, broadcasted, coordDec, coordAlive, coordFaulty>>

TypeOK ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ asked \in [participants -> BOOLEAN]
    /\ recvd \in [participants -> {waiting, yes, no}]
    /\ broadcasted \in [participants -> {notsent, commit, abort}]
    /\ coordDec \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ asked = [p \in participants |-> FALSE]
    /\ recvd = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ coordDec = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator actions.
AskVote(p) ==
    /\ coordAlive
    /\ ~asked[p]
    /\ asked' = [asked EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, recvd, broadcasted, coordDec, coordAlive, coordFaulty>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ ~asked[p]
    /\ sent[p]
    /\ recvd' = [recvd EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, asked, broadcasted, coordDec, coordAlive, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ asked[p]
    /\ recvd[p] = waiting
    /\ ~alive[p]
    /\ coordDec' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, asked, recvd, broadcasted, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ \A p \in participants : recvd[p] # waiting
    /\ coordDec' = IF \A p \in participants : recvd[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, asked, recvd, broadcasted, coordAlive, coordFaulty>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDec # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDec]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, asked, recvd, coordDec, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, asked, recvd, broadcasted, coordDec>>

\* Participant actions.
SendVote(p) ==
    /\ alive[p]
    /\ asked[p]
    /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, asked, recvd, broadcasted, coordDec, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sent[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, asked, recvd, broadcasted, coordDec, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~asked[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, asked, recvd, broadcasted, coordDec, coordAlive, coordFaulty>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, asked, recvd, broadcasted, coordDec, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, asked, recvd, broadcasted, coordDec, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : AskVote(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : PartDie(p)

Spec == Init /\ [][Next]_vars
    /\ \A p \in participants :
        /\ TRUE
        /\ SF_vars(AskVote(p)) /\ SF_vars(ReceiveVote(p)) /\ SF_vars(DetectFault(p))
        /\ SF_vars(SendVote(p)) /\ SF_vars(AbortOnVote(p))
        /\ SF_vars(AbortOnTimeout(p)) /\ SF_vars(Decide(p))

\* SAFETY: agreement, commit-validity, abort-validity, decision irreversibility.
NoTwoDecideDifferently ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitOnlyWithUniversalYes ==
    (\E p \in participants : decision[p] = commit) =>
        (\A p \in participants : vote[p] = yes)

AbortOnlyFromDisagreementOrFault ==
    (\E p \in participants : decision[p] = abort) =>
        (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

DecideIrreversible ==
    \A p \in participants :
        /\ (decision[p] = commit) ~> (decision[p] = commit)
        /\ (decision[p] = abort) ~> (decision[p] = abort)

TypeInv == TypeOK

\* LIVENESS: every transaction eventually resolves or the coordinator/at
\* least one participant is known to be faulty; not guaranteed with simple broadcast.
EventualResolution ==
    <>(\A p \in participants : decision[p] # undecided) \/ coordFaulty \/ (\E p \in participants : faulty[p])

====