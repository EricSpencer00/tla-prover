---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* voted/pResult: each participant's vote; alive: who is up; dResult: final decision.
\* faulty: who has crashed; wsent: who already sent its vote to the coordinator.
\* asked/isSent: coordinator's broadcast bookkeeping per participant.
\* recv: votes received by the coordinator (waiting or the actual vote).
VARIABLES voted, alive, dResult, faulty,
         wsent, asked, recv, coordSend, coordResult, coordAlive, coordFaulty

vars == <<voted, alive, dResult, faulty,
          wsent, asked, recv, coordSend, coordResult, coordAlive, coordFaulty>>

TypeInv ==
    /\ voted \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ dResult \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ wsent \in [participants -> BOOLEAN]
    /\ asked \in [participants -> BOOLEAN]
    /\ recv \in [participants -> {yes, no, waiting}]
    /\ coordSend \in [participants -> {sent, notsent}]
    /\ coordResult \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ voted = [p \in participants |-> no]
    /\ alive = [p \in participants |-> TRUE]
    /\ dResult = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ wsent = [p \in participants |-> FALSE]
    /\ asked = [p \in participants |-> FALSE]
    /\ recv = [p \in participants |-> waiting]
    /\ coordSend = [p \in participants |-> notsent]
    /\ coordResult = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator: send vote request to a participant (simple broadcast is on the decision path).
Ask(p) ==
    /\ coordAlive
    /\ ~asked[p]
    /\ asked' = [asked EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voted, alive, dResult, faulty, wsent,
                   recv, coordSend, coordResult, coordAlive, coordFaulty>>

\* Coordinator: receive a participant's vote, once it has been sent.
RecvVote(p) ==
    /\ coordAlive
    /\ coordResult = undecided
    /\ asked[p]
    /\ recv[p] = waiting
    /\ wsent[p]
    /\ recv' = [recv EXCEPT ![p] = voted[p]]
    /\ UNCHANGED <<voted, alive, dResult, faulty, wsent,
                   asked, coordSend, coordResult, coordAlive, coordFaulty>>

\* Coordinator: detect a participant fault while its vote is still missing.
DetectFault(p) ==
    /\ coordAlive
    /\ coordResult = undecided
    /\ asked[p]
    /\ recv[p] = waiting
    /\ ~alive[p]
    /\ coordResult' = abort
    /\ UNCHANGED <<voted, alive, dResult, faulty, wsent,
                   asked, recv, coordSend, coordAlive, coordFaulty>>

\* Coordinator: decide commit only if every received vote is yes; otherwise abort.
Decide ==
    /\ coordAlive
    /\ coordResult = undecided
    /\ \A p \in participants : recv[p] # waiting
    /\ coordResult' = IF \A p \in participants : recv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<voted, alive, dResult, faulty, wsent,
                   asked, recv, coordSend, coordAlive, coordFaulty>>

\* Coordinator: broadcast its decision to a participant (simple broadcast).
Broadcast(p) ==
    /\ coordAlive
    /\ coordResult # undecided
    /\ coordSend[p] = notsent
    /\ coordSend' = [coordSend EXCEPT ![p] = sent]
    /\ UNCHANGED <<voted, alive, dResult, faulty, wsent,
                   asked, recv, coordResult, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<voted, alive, dResult, faulty, wsent,
                   asked, recv, coordSend, coordResult, coordAlive, coordFaulty>>

\* Participant: send its vote once it has been asked and is still alive.
SendVote(p) ==
    /\ alive[p]
    /\ asked[p]
    /\ ~wsent[p]
    /\ wsent' = [wsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voted, alive, dResult, faulty,
                   asked, recv, coordSend, coordResult, coordAlive, coordFaulty>>

\* Participant: abort unilaterally if its own vote is no.
AbortOnVote(p) ==
    /\ alive[p]
    /\ dResult[p] = undecided
    /\ wsent[p]
    /\ voted[p] = no
    /\ dResult' = [dResult EXCEPT ![p] = abort]
    /\ UNCHANGED <<voted, alive, faulty, wsent,
                   asked, recv, coordSend, coordResult, coordAlive, coordFaulty>>

\* Participant: abort due to coordinator not sending a vote request (timeout).
AbortOnTimeout(p) ==
    /\ alive[p]
    /\ dResult[p] = undecided
    /\ ~coordAlive
    /\ ~asked[p]
    /\ dResult' = [dResult EXCEPT ![p] = abort]
    /\ UNCHANGED <<voted, alive, faulty, wsent,
                   asked, recv, coordSend, coordResult, coordAlive, coordFaulty>>

\* Participant: adopt the coordinator's broadcast decision.
DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ dResult[p] = undecided
    /\ coordSend[p] = sent
    /\ dResult' = [dResult EXCEPT ![p] = coordResult]
    /\ UNCHANGED <<voted, alive, faulty, wsent,
                   asked, recv, coordSend, coordResult, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voted, dResult, wsent,
                   asked, recv, coordSend, coordResult, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : Ask(p)
    \/ \E p \in participants : RecvVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ Decide
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : PartDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : SendVote(p))
        /\ WF_vars(\E p \in participants : AbortOnVote(p))
        /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
        /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
        /\ WF_vars(\E p \in participants : RecvVote(p))
        /\ WF_vars(\E p \in participants : Broadcast(p))
        /\ WF_vars(Decide)

\* Safety: no two participants decide differently.
AllDecideConsistently ==
    \A p1, p2 \in participants :
        (dResult[p1] = commit /\ dResult[p2] = abort) => FALSE

\* Safety: a commit needs every vote to be yes.
CommitValid ==
    \A p \in participants : dResult[p] = commit => \A q \in participants : voted[q] = yes

\* Safety: an abort needs a no vote, or a participant fault, or a coordinator fault.
AbortValid ==
    \A p \in participants : dResult[p] = abort =>
        \/ \E q \in participants : voted[q] = no
        \/ \E q \in participants : faulty[q]
        \/ coordFaulty

\* Safety: a participant decides at most once (irrevocability per outcome).
DecideAtMostOnce ==
    \A p \in participants :
        /\ (dResult[p] = commit => dResult' = [dResult EXCEPT ![p] = commit])
        /\ (dResult[p] = abort => dResult' = [dResult EXCEPT ![p] = abort])

\* Liveness: everyone decides, or someone has crashed.
Resolution ==
    <>(\E p \in participants : dResult[p] # undecided)
        \/ \E p \in participants : faulty[p]
        \/ coordFaulty

====