---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: what decision has been pre-received (or notsent), plus
\* which other participants it has been forwarded to.
\* Each participant's own entry holds the pre-decision itself.
\* The forwarding table is what guarantees termination even after coordinator crash.
Entries == {notsent, commit, abort}

VARIABLES vote, alive, decision, faulty, voteSent, fwd, coordCrash, coordDecide, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty voteSent, fwd, coordCrash, coordDecide, coordAlive, coordFaulty>>

TypeOK ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {waiting, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \subseteq participants
    /\ fwd \in [participants -> [participants -> Entries]]
    /\ coordCrash \in [participants -> BOOLEAN]
    /\ coordDecide \in [participants -> {notsent, commit, abort}]
    /\ coordAlive \in [participants -> BOOLEAN]
    /\ coordFaulty \in [participants -> BOOLEAN]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = {}
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
    /\ coordCrash = [p \in participants |-> FALSE]
    /\ coordDecide = [p \in participants |-> notsent]
    /\ coordAlive = [p \in participants |-> TRUE]
    /\ coordFaulty = [p \in participants |-> FALSE]

SendRequest(p) ==
    /\ coordAlive[p]
    /\ coordDecide[p] = notsent
    /\ \A q \in participants: vote[q] = undecided
    /\ \A q \in participants: coordAlive[q]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, fwd, coordCrash, coordDecide, coordAlive, coordFaulty>>

\* Voter records a yes/no ballot and acknowledges it to the coordinator.
GetVote(p, v) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ vote[p] = undecided
    /\ v \in {yes, no}
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ voteSent' = voteSent \cup {p}
    /\ UNCHANGED <<alive, decision, faulty, fwd, coordCrash, coordDecide, coordAlive, coordFaulty>>

DetectCoordFault(p) ==
    /\ coordAlive[p]
    /\ coordAlive' = [coordAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, fwd, coordCrash, coordDecide, coordFaulty>>

MakeDecision(p) ==
    /\ coordAlive[p]
    /\ coordDecide[p] = notsent
    /\ \A q \in participants: fwd[p][q] = notsent
    /\ coordDecide' = [coordDecide EXCEPT ![p] = IF \A q \in participants: vote[q] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, fwd, coordCrash, coordAlive, coordFaulty>>

\* 1-to-1 broadcast only, queued by the coordinator; forwarded later by participants.
Broadcast(p, q) ==
    /\ coordAlive[p]
    /\ coordDecide[p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = coordDecide[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordCrash, coordDecide, coordAlive, coordFaulty>>

Die(p) ==
    /\ ~faulty[p]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, voteSent, fwd, coordCrash, coordDecide, coordAlive, coordFaulty>>

\* Participant receives a pre-decision broadcast from the coordinator.
PreDecideCoord(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ fwd[p][p] = notsent
    /\ \E q \in participants: fwd[q][p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[CHOOSE q \in participants: fwd[q][p] # notsent][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordCrash, coordDecide, coordAlive, coordFaulty>>

\* Participant receives a pre-decision forwarded by another participant.
PreDecideFwd(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ fwd[p][p] = notsent
    /\ \E q \in participants: fwd[q][p] \in {commit, abort}
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[CHOOSE q \in participants: fwd[q][p] \in {commit, abort}][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordCrash, coordDecide, coordAlive, coordFaulty>>

\* Forwarder propagates its pre-decision to another participant.
Forward(p, q) ==
    /\ alive[p]
    /\ fwd[p][p] \in {commit, abort}
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordCrash, coordDecide, coordAlive, coordFaulty>>

\* The non-blocking guarantee: once everybody else has been forwarded to, finalize locally.
Decide(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ fwd[p][p] \in {commit, abort}
    /\ \A q \in participants: fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, fwd, coordCrash, coordDecide, coordAlive, coordFaulty>>

\* Abort by timeout if the coordinator is dead and no broadcast or forwarding can arrive.
AbortTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ ~coordAlive[p]
    /\ \A q \in participants: fwd[q][p] = notsent
    /\ \A q \in participants: ~faulty[q] \/ fwd[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, fwd, coordCrash, coordDecide, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants: SendRequest(p) \/ DetectCoordFault(p) \/ MakeDecision(p) \/ Die(p)
    \/ \E p \in participants, q \in participants: Broadcast(p, q) \/ Forward(p, q)
    \/ \E p \in participants, v \in {yes, no}: GetVote(p, v)
    \/ \E p \in participants: PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p) \/ AbortTimeout(p)

Coordinated ==
    \E p \in participants: SendRequest(p) /\ coordAlive[p]

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(Coordinated)
    /\ \A p \in participants: SF_vars(\E q \in participants: PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p) \/ AbortTimeout(p))

\* Safety: two participants can never commit and abort at once.
AC1 ==
    \A p, q \in participants: ~(decision[p] = commit /\ decision[q] = abort)

\* Safety: a commit requires unanimous yes votes.
AC2 ==
    \A p \in participants: decision[p] = commit => (\A q \in participants: vote[q] = yes)

\* Safety: an abort must be justified by a no vote or a fault.
AC3 ==
    \A p \in participants:
        decision[p] = abort =>
            \E q \in participants: vote[q] = no \/ faulty[q] \/ coordFaulty[q]

\* Safety: a decision is final once made.
AC4 ==
    \A p \in participants: (decision[p] # waiting) ~> (decision[p] # waiting)

\* Liveness: every non-faulty participant eventually decides.
AC5 ==
    \A p \in participants: ~faulty[p] ~> (decision[p] # waiting \/ faulty[p])

SpecProperties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC5

TypeInvNB == TypeOK

====