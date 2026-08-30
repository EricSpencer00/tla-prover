---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB extends ACP-SB with a reliable broadcast: a participant forwards
\* the pre-decision to all others before finalizing it. Participants may
\* crash silently at any time (the coordinator as well).
VARIABLES vote, alive, decision, faulty, votesent, req, cvote, broadcast, cdecision, alivenow, fwd

vars == <<vote, alive, decision, faulty, votesent, req, cvote, broadcast,
           cdecision, alivenow, fwd>>

Bump(v) == IF v = yes THEN no ELSE IF v = no THEN yes ELSE no

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in {waiting, commit, abort}
    /\ faulty \in [participants -> BOOLEAN]
    /\ votesent \in [participants -> BOOLEAN]
    /\ req \in BOOLEAN
    /\ cvote \in {yes, no, undecided}
    /\ broadcast \subseteq participants
    /\ cdecision \in {commit, abort, undecided}
    /\ alivenow \in [participants -> BOOLEAN]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* The coordinator gathers votes, then broadcasts its decision to every
\* participant. A participant may learn the decision from the coordinator
\* or from a peer's forwarded message, whichever arrives first.
Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = waiting
    /\ faulty = [p \in participants |-> FALSE]
    /\ votesent = [p \in participants |-> FALSE]
    /\ req = FALSE
    /\ cvote = undecided
    /\ broadcast = {}
    /\ cdecision = undecided
    /\ alivenow = [p \in participants |-> TRUE]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ decision = waiting
    /\ req' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cvote,
                   broadcast, cdecision, alivenow, fwd>>

GetVote(p) ==
    /\ req
    /\ alive[p]
    /\ vote[p] = undecided
    /\ votesent[p] = FALSE
    /\ vote' = [vote EXCEPT ![p] = IF Bump(cvote) = yes THEN yes ELSE no]
    /\ cvote' = IF cvote = undecided THEN Bump(cvote) ELSE Bump(Bump(cvote))
    /\ votesent' = [votesent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, req, broadcast, cdecision,
                   alivenow, fwd>>

\* The coordinator may crash silently, which is precisely why peers forward.
CoordinatorDead ==
    /\ decision = waiting
    /\ req
    /\ decision' = waiting
    /\ faulty' = [faulty EXCEPT ![CHOOSE p \in participants : TRUE] = TRUE]
    /\ alivenow' = [p \in participants |-> IF p = CHOOSE q \in participants : TRUE
                                          THEN FALSE ELSE alivenow[p]]
    /\ UNCHANGED <<vote, alive, cvote, votesent, req, broadcast,
                   cdecision, fwd>>

MakeDecision ==
    /\ decision = waiting
    /\ \A p \in participants : votesent[p] /\ alive[p]
    /\ cdecision' = IF cvote = yes THEN commit ELSE abort
    /\ decision' = waiting
    /\ UNCHANGED <<vote, alive, faulty, votesent, req, cvote,
                   broadcast, alivenow, fwd>>

Broadcast(p) ==
    /\ decision = waiting
    /\ alive[p]
    /\ broadcast' = broadcast \cup {p}
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cvote,
                   cdecision, alivenow, fwd>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ alivenow' = [alivenow EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<vote, decision, cvote, votesent, req, broadcast,
                   cdecision, fwd>>

PreDecideCoord(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ p \in broadcast
    /\ fwd' = [fwd EXCEPT ![p][p] = IF cdecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cvote,
                   broadcast, cdecision, alivenow>>

PreDecideForward(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in participants : q # p /\ fwd[q][p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = IF \E q \in participants : q # p /\ fwd[q][p] = commit
                                   THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cvote,
                   broadcast, cdecision, alivenow>>

Forward(p, q) ==
    /\ alive[p]
    /\ fwd[p][p] # notsent
    /\ q # p
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cvote,
                   broadcast, cdecision, alivenow>>

Decide(p) ==
    /\ alive[p]
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ decision' = IF fwd[p][p] = commit THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, faulty, votesent, req, cvote, broadcast,
                   cdecision, alivenow, fwd>>

AbortTimeout(p) ==
    /\ alive[p]
    /\ decision = waiting
    /\ ~alive[CHOOSE q \in participants : TRUE]
    /\ broadcast = {}
    /\ \A q \in participants : ~(\A d \in participants : fwd[d][q] # notsent)
    /\ decision' = abort
    /\ UNCHANGED <<vote, alive, faulty, votesent, req, cvote,
                   broadcast, cdecision, alivenow, fwd>>

Next ==
    \/ SendRequest
    \/ CoordinatorDead
    \/ MakeDecision
    \/ \E p \in participants :
         \/ GetVote(p) \/ Broadcast(p) \/ Die(p) \/ PreDecideCoord(p)
         \/ PreDecideForward(p) \/ Decide(p) \/ AbortTimeout(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(PreDecideCoord(CHOOSE p \in participants : TRUE))
    /\ WF_vars(PreDecideForward(CHOOSE p \in participants : TRUE))
    /\ WF_vars(Decide(CHOOSE p \in participants : TRUE))
    /\ WF_vars(\E p \in participants : AbortTimeout(p))
    /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))

\* Safety: agreement and validity hold regardless of who crashes.
AC1 == \A p \in participants, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) =>
        (\E p \in participants : vote[p] = no \/ faulty[p] \/ cdecision = abort)
AC4 == \A p \in participants : (decision[p] # waiting) ~> (decision[p] = decision[p])

\* Progress: every non-faulty participant decides, even if the coordinator dies.
AC3Live == <>(\A p \in participants : decision[p] # waiting \/ faulty[p] \/ cdecision # undecided)
AC5 == \A p \in participants : (alive[p] /\ decision[p] = waiting) ~> (decision[p] # waiting \/ faulty[p])

Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC3Live /\ AC5

====