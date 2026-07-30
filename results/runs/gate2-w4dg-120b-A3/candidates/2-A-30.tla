---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voted, sent, coord

TypeInvNB ==
    /\ pstate \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ coord \in [state : {waiting, yes, no, decided},
                 v : {yes, no, undecided},
                 broadcast : [participants -> {notsent, commit, abort}]]

\* Forwarding table: what this participant has received (at its own index) and
\* which other participants it has already forwarded that received decision to.
forward == [c \in participants |-> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ pstate = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ coord = [state |-> waiting, v |-> undecided, broadcast |-> [p \in participants |-> notsent]]
    /\ forward = [c \in participants |-> [p \in participants |-> notsent]]

\* Coordinator actions: unchanged from the simple broadcast variant (ACP-SB).
SendReq ==
    /\ coord.state = waiting
    /\ coord' = [coord EXCEPT !.state = yes]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, forward>>

GetVote(p) ==
    /\ coord.state = yes
    /\ alive[p]
    /\ ~voted[p]
    /\ pstate' = [pstate EXCEPT ![p] = yes]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, sent, coord, forward>>

DetectFault(p) ==
    /\ coord.state = yes
    /\ alive[p]
    /\ pstate[p] = yes
    /\ sent[p] = FALSE
    /\ coord' = [coord EXCEPT !.state = no]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, forward>>

DecideCoord ==
    /\ coord.state = yes
    /\ coord.state' = decided
    /\ coord'' = [coord EXCEPT !.v = yes]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, forward>>

AbortCoord ==
    /\ coord.state = no
    /\ coord.state' = decided
    /\ coord'' = [coord EXCEPT !.v = no]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, forward>>

BroadcastCoord(p) ==
    /\ coord.state = decided
    /\ alive[p]
    /\ coord.broadcast[p] = notsent
    /\ coord' = [coord EXCEPT !.broadcast[p] = coord.v]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, forward>>

DieCoord ==
    /\ coord.state # decided
    /\ coord.state' = decided
    /\ coord'' = [coord EXCEPT !.v = no]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, forward>>

\* Participant pre-decision from the coordinator's broadcast.
PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coord.broadcast[p] # notsent
    /\ forward[p][p] = notsent
    /\ forward' = [forward EXCEPT ![p][p] = coord.broadcast[p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, coord>>

\* Participant pre-decision from another participant's forwarded decision.
PreDecideFromPeer(p, q) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ p # q
    /\ forward[q][p] # notsent
    /\ forward[p][p] = notsent
    /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, coord>>

\* Forward the pre-decision to another participant.
Forward(p, q) ==
    /\ alive[p]
    /\ forward[p][p] # notsent
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, coord>>

\* A participant finalizes only after having forwarded to everyone else.
Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forward[p][p] # notsent
    /\ \A q \in participants \ {p} : forward[p][q] = forward[p][p]
    /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
    /\ UNCHANGED <<pstate, alive, faulty, voted, sent, coord, forward>>

\* Abort on timeout if the coordinator has died and no one can forward.
AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coord.state = decided
    /\ coord.v = no
    /\ \A q \in participants : coord.broadcast[q] = notsent
    /\ \A q \in participants : faulty[q] \/ alive[q]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pstate, alive, faulty, voted, sent, coord, forward>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pstate, sent, coord, forward>>

NextNB ==
    \/ SendReq
    \/ DecideCoord
    \/ AbortCoord
    \/ BroadcastCoord('player')
    \/ DieCoord
    \/ \E p \in participants : GetVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : \E q \in participants : PreDecideFromPeer(p, q)
    \/ \E p \in participants : Decide(p)

SpecNB == InitNB /\ [][NextNB]_<<pstate, alive, decision, faulty, voted, sent, coord, forward>>

\* Safety: no two participants disagree on the final outcome.
AC1 ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

\* Commit only when everyone voted yes.
AC2 ==
    \A p \in participants :
        decision[p] = commit => (\A q \in participants : pstate[q] = yes)

\* Abort only if some participant voted no, or some participant is faulty,
\* or the coordinator is faulty.
AC3 ==
    \A p \in participants :
        decision[p] = abort => (\/ \E q \in participants : pstate[q] = no
                                 \/ \E q \in participants : faulty[q]
                                 \/ coord.v = no)

\* Irreversibility: a decided outcome never changes.
AC4 ==
    \A p \in participants :
        (decision[p] = commit \/ decision[p] = abort) => (decision[p] = decision[p])

\* Liveness: every non-faulty participant eventually decides.
AC5 ==
    \A p \in participants :
        (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

\* Liveness: the protocol makes progress towards a decision, a fault, or a
\* coordinator failure.
AC3Progress ==
    <>(\A p \in participants : decision[p] # undecided)
        \/ <>(\E p \in participants : faulty[p])
        \/ <>(coord.v = no)

====