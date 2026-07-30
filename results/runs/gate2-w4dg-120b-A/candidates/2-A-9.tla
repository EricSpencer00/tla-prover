---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast: each participant forwards its pre-decision to EVERY other
\* participant before it may finalize locally. The forwarding table records both
\* what decision a participant has received and what it has forwarded on.

VARIABLES pstate, alive, decision, faulty, voted, widereq, wvote, wbc, wdec, wcoordAlive, wcoordFaulty, fwd

vars == <<pstate, alive, decision, faulty, voted, widereq, wvote, wbc, wdec, wcoordAlive, wcoordFaulty, fwd>>

TypeInvNB ==
    /\ pstate \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, waiting}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ widereq \in BOOLEAN
    /\ wvote \in BOOLEAN
    /\ wbc \in BOOLEAN
    /\ wdec \in {commit, abort}
    /\ wcoordAlive \in BOOLEAN
    /\ wcoordFaulty \in BOOLEAN
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ pstate = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]
    /\ widereq = FALSE
    /\ wvote = FALSE
    /\ wbc = FALSE
    /\ wdec = commit
    /\ wcoordAlive = TRUE
    /\ wcoordFaulty = FALSE
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator's actions are unchanged from the base simple broadcast spec:
SendReq ==
    /\ wcoordAlive
    /\ ~widereq
    /\ widereq' = TRUE
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, wvote, wbc, wdec, wcoordAlive, wcoordFaulty, fwd>>

GetVote(p) ==
    /\ wcoordAlive
    /\ widereq
    /\ alive[p]
    /\ ~voted[p]
    /\ pstate[p] \in {yes, no}
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, alive, decision, faulty, widereq, wvote, wbc, wdec, wcoordAlive, wcoordFaulty, fwd>>

CoordinatorDetect ==
    /\ wcoordAlive
    /\ widereq
    /\ ~wvote
    /\ \E p \in participants : voted[p]
    /\ wvote' = TRUE
    /\ UNCHANGED <<pstate, alive, decision, faulty, widereq, wbc, wdec, wcoordAlive, wcoordFaulty, fwd>>

MakeDecision ==
    /\ wcoordAlive
    /\ wvote
    /\ ~wbc
    /\ wdec' = IF (\A p \in participants : pstate[p] = yes) THEN commit ELSE abort
    /\ wbc' = TRUE
    /\ UNCHANGED <<pstate, alive, decision, faulty, widereq, wvote, widereq, wcoordAlive, wcoordFaulty, fwd>>

BroadcastDec ==
    /\ wcoordAlive
    /\ wbc
    /\ \E p \in participants : fwd[p][p] = notsent
    /\ \E p \in participants : fwd' = [fwd EXCEPT ![p][p] = wdec]
    /\ UNCHANGED <<pstate, alive, decision, faulty, widereq, wvote, wbc, wdec, wcoordAlive, wcoordFaulty>>

CoordinatorDie ==
    /\ wcoordAlive
    /\ wcoordAlive' = FALSE
    /\ wcoordFaulty' = TRUE
    /\ UNCHANGED <<pstate, alive, decision, faulty, widereq, voted, wvote, wbc, wdec, fwd>>

\* A participant first stores an incoming decision (from the coordinator or a peer)
\* in its own forwarding entry before it may forward it on.
PreDecideFromCoordinator(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ wbc
    /\ fwd' = [fwd EXCEPT ![p][p] = wdec]
    /\ UNCHANGED <<pstate, alive, decision, faulty, widereq, voted, wvote, wbc, wdec, wcoordAlive, wcoordFaulty>>

PreDecideFromOther(q, p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ fwd[q][p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, widereq, voted, wvote, wbc, wdec, wcoordAlive, wcoordFaulty>>

Forward(p, q) ==
    /\ alive[p]
    /\ p # q
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, widereq, voted, wvote, wbc, wdec, wcoordAlive, wcoordFaulty>>

Decide(p) ==
    /\ alive[p]
    /\ \A q \in participants \ {p} : fwd[p][q] # notsent
    /\ decision[p] = waiting
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<pstate, alive, faulty, widereq, voted, wvote, wbc, wdec, wcoordAlive, wcoordFaulty, fwd>>

AbortTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ ~wcoordAlive
    /\ \A q \in participants : fwd[q][p] = notsent
    /\ \A q \in participants : faulty[q]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pstate, alive, faulty, widereq, voted, wvote, wbc, wdec, wcoordAlive, wcoordFaulty, fwd>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, decision, widereq, wvote, wbc, wdec, wcoordAlive, wcoordFaulty, fwd>>

CoordProgress == SendReq \/ CoordinatorDetect \/ MakeDecision \/ BroadcastDec \/ CoordinatorDie
PartProgress == (\E p \in participants : GetVote(p)) \/ (\E p \in participants : PreDecideFromCoordinator(p))
    \/ (\E q, p \in participants : PreDecideFromOther(q, p))
    \/ (\E p, q \in participants : Forward(p, q))
    \/ (\E p \in participants : Decide(p)) \/ (\E p \in participants : AbortTimeout(p))

NextNB ==
    \/ CoordProgress \/ PartProgress
    \/ (\E p \in participants : Die(p))

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(PartProgress)
    /\ SF_vars(CoordProgress)

\* Safety: the action reduces to the base case, but the forwarding path is
\* the new twist -- it must not silently break agreement.
AC1 == ~(\E p, q \in participants : decision[p] = commit /\ decision[q] = abort)

AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : pstate[q] = yes)

AC3 == (\E p \in participants : decision[p] = abort) =>
        (\E q \in participants : pstate[q] = no \/ faulty[q] \/ wcoordFaulty)

AC4 == (\A p \in participants : (decision[p] = commit) ~> (decision[p] = commit))
        /\ (\A p \in participants : (decision[p] = abort) ~> (decision[p] = abort))

\* Liveness: every non-faulty participant eventually decides, even though the
\* coordinator may crash mid-broadcast -- that's the point of the forwarding.
AC5 == (\A p \in participants : (alive[p] /\ decision[p] = waiting) ~> (decision[p] # waiting))

====