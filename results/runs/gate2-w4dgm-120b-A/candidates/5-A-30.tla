---- MODULE ACP_SB ----
EXTENDS Naturals

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).  A single
\* coordinator collects participant votes and broadcasts one decision;
\* a crash during broadcast can strand participants undecided, which is why
\* this simple-broadcast variant is blocking (it does NOT satisfy AC5).
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, asked, recv, sent

vars == <<vote, alive, decision, faulty, voted, asked, recv, sent>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]

    /\ asked \in [participants -> {waiting, notsent}]
    /\ recv \in [participants -> {yes, no, waiting}]
    /\ sent \in [participants -> {commit, abort, notsent}]

    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]

    /\ asked = [p \in participants |-> waiting]
    /\ recv = [p \in participants |-> waiting]
    /\ sent = [p \in participants |-> notsent]

    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided

\* Coordinator actions.
RequestVote(p) ==
    /\ coordAlive
    /\ asked[p] = waiting
    /\ asked' = [asked EXCEPT ![p] = notsent]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, recv, sent, coordAlive, coordFaulty, coordDecision>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : asked[q] = notsent
    /\ recv[p] = waiting
    /\ voted[p]
    /\ recv' = [recv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, asked, sent, coordAlive, coordFaulty, coordDecision>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : asked[q] = notsent
    /\ recv[p] = waiting
    /\ ~alive[p]
    /\ ~voted[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, asked, recv, sent, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : recv[p] # waiting
    /\ coordDecision' = IF \A p \in participants : recv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, asked, recv, sent, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ sent[p] = notsent
    /\ sent' = [sent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, asked, recv, coordAlive, coordFaulty, coordDecision>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, asked, recv, sent, coordDecision>>

\* Participant actions.
SendVote(p) ==
    /\ alive[p]
    /\ asked[p] = notsent
    /\ ~voted[p]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, asked, recv, sent, coordAlive, coordFaulty, coordDecision>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ voted[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, asked, recv, sent, coordAlive, coordFaulty, coordDecision>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ asked[p] = waiting
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, asked, recv, sent, coordAlive, coordFaulty, coordDecision>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = sent[p]]
    /\ UNCHANGED <<vote, alive, faulty, voted, asked, recv, sent, coordAlive, coordFaulty, coordDecision>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voted, asked, recv, sent, coordAlive, coordFaulty, coordDecision>>

\* At least one of the two actors is always able to act, so weak fairness is
\* applied to all of them except the death steps (which stay unfair).
Next ==
    \/ \E p \in participants : RequestVote(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
    \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ Decide(p) \/ PartDie(p)
    \/ MakeDecision
    \/ CoordDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants :
        /\ TRUE
        /\ WF_vars(RequestVote(p))
        /\ WF_vars(ReceiveVote(p))
        /\ WF_vars(DetectFault(p))
        /\ WF_vars(BroadcastDecision(p))
        /\ WF_vars(SendVote(p))
        /\ WF_vars(AbortOnVote(p))
        /\ WF_vars(AbortOnTimeout(p))
        /\ WF_vars(Decide(p))
    /\ WF_vars(MakeDecision)

\* Safety: no two participants ever decide differently; a commit requires
\* unanimity, an abort requires at least one no vote or a fault.
Agreement ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            \E q \in participants : vote[q] = no \/ faulty[q] \/ coordFaulty

Irreversible ==
    \A p \in participants :
        /\ (decision[p] = commit) ~> (decision[p] = commit)
        /\ (decision[p] = abort) ~> (decision[p] = abort)

\* Liveness: every transaction eventually resolves or crashes somewhere --
\* not guaranteed under simple broadcast (blocked if the coordinator dies mid-
\* broadcast), but at least one of the resolution/failure cases always
\* happens.
ResolveOrCrash ==
    <>(\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

====