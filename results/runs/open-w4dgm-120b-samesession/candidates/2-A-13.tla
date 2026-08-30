---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

\* Non-blocking atomic commitment via reliable broadcast: a participant stores
\* a pre-decision it receives (from the coordinator or from another participant)
\* and forwards it to every other participant before finalizing locally. If the
\* coordinator crashes mid-broadcast, forwarding by the surviving participants
\* is what keeps the protocol terminating for all non-faulty participants.
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* forward[p][q] is what p has sent to q: not-sent, commit, or abort.
VARIABLES vote, alive, decision, faulty, voteSent, forward

vars == <<vote, alive, decision, faulty, voteSent, forward>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ vote = [p \in participants |-> yes]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

Decide(p) == IF \A q \in participants : forward[p][q] # notsent THEN vote[p] ELSE undecided

SendVote(p) ==
    /\ alive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, forward>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ vote[p] = no
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forward>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants : alive[q]
    /\ ~\E q \in participants : forward[q][p] # notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forward>>

\* A participant stores a pre-decision the coordinator broadcast to it.
PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forward[p][p] = notsent
    /\ forward[p][p] # notsent
    /\ decision' = [decision EXCEPT ![p] = Decide(p)]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forward>>

\* A participant stores a pre-decision another participant forwarded to it.
PreDecideFromForward(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \E q \in participants : q # p /\ forward[q][p] # notsent
    /\ decision' = [decision EXCEPT ![p] = Decide(p)]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forward>>

\* Forward a received pre-decision to another participant.
ForwardTo(p, q) ==
    /\ alive[p]
    /\ decision[p] # undecided
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = Decide(p)]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

DecideNonBlocking(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants : forward[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = Decide(p)]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forward>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voteSent, forward>>

Next ==
    \/ \E p \in participants :
        \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
        \/ PreDecideFromCoord(p) \/ PreDecideFromForward(p)
        \/ DecideNonBlocking(p) \/ Die(p)
        \/ \E q \in participants : ForwardTo(p, q)

SpecNB == Init /\ [][Next]_vars
    /\ \A p \in participants : WF_vars(PreDecideFromCoord(p)) /\ WF_vars(PreDecideFromForward(p))
    /\ \A p, q \in participants : WF_vars(ForwardTo(p, q))

\* Safety: no two participants reach different decisions.
AC1 == \A p, q \in participants : (decision[p] = commit) => (decision[q] # abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) =>
            (\E p \in participants : vote[p] = no \/ faulty[p] \/ faulty[Choose q \in participants : TRUE])
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* Liveness: every non-faulty participant eventually decides.
AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====