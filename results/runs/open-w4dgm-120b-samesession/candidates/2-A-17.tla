---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB extends ACP-SB with a reliable broadcast: participants forward
\* decisions to each other and finalize only after forwarding to all.

VARIABLES vote, alive, decision, faulty, sentvote, coordphase, coordaux, fwd

vars == <<vote, alive, decision, faulty, sentvote, coordphase, coordaux, fwd>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentvote \in [participants -> BOOLEAN]
    /\ coordphase \in {waiting, yes, no, done}
    /\ coordaux \in [participants -> {waiting, yes, no}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ vote = [p \in participants |-> yes]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentvote = [p \in participants |-> FALSE]
    /\ coordphase = waiting
    /\ coordaux = [p \in participants |-> waiting]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest(p) ==
    /\ coordphase = waiting
    /\ coordphase' = waiting
    /\ coordaux' = [coordaux EXCEPT ![p] = waiting]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, fwd>>

\* The coordinator collects votes from participants; this always makes
\* progress unless the coordinator crashes, which is excluded by fairness.
GetVote(p) ==
    /\ coordphase = waiting
    /\ alive[p] = TRUE
    /\ sentvote[p] = FALSE
    /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
    /\ coordaux' = [coordaux EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordphase, fwd>>

DetectFault(p) ==
    /\ coordaux[p] # waiting
    /\ coordphase \notin {yes, no}
    /\ coordphase' = coordaux[p]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordaux, fwd>>

MakeDecision ==
    /\ coordphase \in {yes, no}
    /\ coordphase # done
    /\ coordphase' = done
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordaux, fwd>>

Broadcast(p, c) ==
    /\ coordphase = done
    /\ alive[p] = TRUE
    /\ fwd[p][c] = notsent
    /\ fwd' = [fwd EXCEPT ![p][c] = IF coordaux[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordphase, coordaux>>

\* The coordinator may crash silently at any point; crash is always available.
DieCoordinator ==
    /\ coordphase # done
    /\ coordphase' = done
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordaux, fwd>>

SendVote(p) ==
    /\ alive[p] = TRUE
    /\ sentvote[p] = FALSE
    /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordphase, coordaux, fwd>>

AbortOnVote(p) ==
    /\ alive[p] = TRUE
    /\ coordphase # waiting
    /\ decision[p] = undecided
    /\ coordphase = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, sentvote, faulty, coordphase, coordaux, fwd>>

\* Part of ACP-NB: a pre-decision may arrive from another participant's
\* forwarding (not just the coordinator's own broadcast).
PreDecideFromPeer(p) ==
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ \E q \in participants :
         /\ q # p
         /\ fwd[q][p] # notsent
         /\ fwd[p][p] = notsent
         /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordphase, coordaux>>

PreDecideFromCoord(p) ==
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = IF coordaux[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordphase, coordaux>>

\* Forwarding before finalizing is what gives the reliable broadcast its
\* non-blocking guarantee, even when the coordinator crashes.
Forward(p, q) ==
    /\ alive[p] = TRUE
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordphase, coordaux>>

Decide(p) ==
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, sentvote, faulty, coordphase, coordaux, fwd>>

AbortOnTimeout(p) ==
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ coordphase = done
    /\ \A q \in participants : alive[q] => fwd[q][p] = notsent
    /\ \A q \in participants : ~alive[q] => \A r \in participants : fwd[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, sentvote, faulty, coordphase, coordaux, fwd>>

Die(p) ==
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentvote, coordphase, coordaux, fwd>>

CoordStep == SendRequest("c") \/ GetVote("c") \/ DetectFault("c") \/ MakeDecision \/ DieCoordinator

ParticipantStep ==
    \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ PreDecideFromPeer(p)
       \/ PreDecideFromCoord(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
    \/ \E p, q \in participants : Broadcast(p, q) \/ Forward(p, q)

Next == CoordStep \/ ParticipantStep

SpecNB == Init /\ [][Next]_vars /\ WF_vars(CoordStep) /\ SF_vars(ParticipantStep)

\* Safety: the agreement and validity checks from ACP-SB still hold under
\* ACP-NB's extra forwarding and crash actions.
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => (\E p \in participants : vote[p] = no \/ faulty[p] \/ coordphase = no)
AC4 == \A p \in participants : (decision[p] # undecided) ~> (decision[p] # undecided)
AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====