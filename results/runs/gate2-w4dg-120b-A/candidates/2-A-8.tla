---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table: for each participant, a map from every participant to the
\* status of the pre-decision received from that participant (not-sent/commit/abort).
VARIABLES vote, alive, decision, faulty, voted, req, pvote, broadcasted, cdecision, pforward

vars == << vote, alive, decision, faulty, voted, req, pvote, broadcasted, cdecision, pforward >>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ req \in {waiting, yes, no}
    /\ pvote \in {yes, no, undecided}
    /\ broadcasted \subseteq participants
    /\ cdecision \in {undecided, commit, abort}
    /\ pforward \in [participants -> [participants -> {notsent, commit, abort}]]

NullFwd ==
    [p \in participants |-> notsent]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]
    /\ req = waiting
    /\ pvote = undecided
    /\ broadcasted = {}
    /\ cdecision = undecided
    /\ pforward = [p \in participants |-> NullFwd]

\* Coordinator begins a new round; all participants' forwarding tables reset.
Request ==
    /\ req = waiting
    /\ req' = yes
    /\ pforward' = [p \in participants |-> NullFwd]
    /\ UNCHANGED << vote, alive, decision, faulty, voted, pvote, broadcasted, cdecision >>

\* A participant votes once a request is in flight.
Vote(p) ==
    /\ req \in {yes, no}
    /\ alive[p] /\ ~voted[p]
    /\ vote' = [vote EXCEPT ![p] = req]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED << alive, decision, faulty, req, pvote, broadcasted, cdecision, pforward >>

\* Coordinator detects a no vote, preparing to abort.
DetectFault ==
    /\ req = yes
    /\ \E p \in participants : vote[p] = no
    /\ pvote' = no
    /\ UNCHANGED << vote, alive, decision, faulty, voted, req, broadcasted, cdecision, pforward >>

\* Coordinator votes yes with nobody voting no.
Decide ==
    /\ req = yes
    /\ \A p \in participants : vote[p] # no
    /\ pvote' = yes
    /\ UNCHANGED << vote, alive, decision, faulty, voted, req, broadcasted, cdecision, pforward >>

\* Broadcast the coordinator's decision to a participant.
Broadcast(p) ==
    /\ req # waiting
    /\ pvote # undecided
    /\ alive[p]
    /\ p \notin broadcasted
    /\ broadcasted' = broadcasted \cup {p}
    /\ UNCHANGED << vote, alive, decision, faulty, voted, req, pvote, cdecision, pforward >>

\* Coordinator crashes silently.
CoordDie ==
    /\ req # waiting
    /\ UNCHANGED << vote, alive, decision, faulty, voted, req, pvote, broadcasted, cdecision, pforward >>

\* A participant receives a pre-decision directly from the coordinator.
PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ p \in broadcasted
    /\ pvote # undecided
    /\ pforward' = [pforward EXCEPT ![p][p] = IF pvote = yes THEN commit ELSE abort]
    /\ UNCHANGED << vote, alive, decision, faulty, voted, req, pvote, broadcasted, cdecision >>

\* A participant receives a pre-decision forwarded from another participant.
PreDecideFromFwd(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ pforward[p][p] = notsent
    /\ \E q \in participants :
         /\ q # p
         /\ pforward[q][p] # notsent
         /\ pforward' = [pforward EXCEPT ![p][p] = pforward[q][p]]
    /\ UNCHANGED << vote, alive, decision, faulty, voted, req, pvote, broadcasted, cdecision >>

\* Forward a received pre-decision to another participant.
Fwd(p, q) ==
    /\ alive[p]
    /\ pforward[p][p] # notsent
    /\ pforward[p][q] = notsent
    /\ pforward' = [pforward EXCEPT ![p][q] = pforward[p][p]]
    /\ UNCHANGED << vote, alive, decision, faulty, voted, req, pvote, broadcasted, cdecision >>

\* Once a participant has forwarded its pre-decision to everyone, it decides.
DecideNB(p) ==
    /\ alive[p]
    /\ pforward[p][p] # notsent
    /\ \A q \in participants : pforward[p][q] # notsent
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = pforward[p][p]]
    /\ UNCHANGED << vote, alive, faulty, voted, req, pvote, broadcasted, cdecision, pforward >>

\* Abort on timeout when nothing is in flight and nobody is forwarding anything to us.
TimeoutAbort(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ req = waiting
    /\ \A q \in participants :
         \/ ~alive[q]
         \/ p \notin broadcasted
         \/ pforward[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, voted, req, pvote, broadcasted, cdecision, pforward >>

\* Crash a participant silently.
Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, voted, req, pvote, broadcasted, cdecision, pforward >>

Next ==
    \/ Request \/ DetectFault \/ Decide \/ CoordDie
    \/ \E p \in participants :
         \/ Vote(p) \/ Broadcast(p) \/ PreDecideFromCoord(p)
         \/ PreDecideFromFwd(p) \/ DecideNB(p) \/ TimeoutAbort(p) \/ Die(p)
         \/ \E q \in participants : Fwd(p, q)

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : Vote(p))
    /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
    /\ WF_vars(\E p \in participants : PreDecideFromFwd(p))
    /\ WF_vars(\E p \in participants : \E q \in participants : Fwd(p, q))
    /\ WF_vars(\E p \in participants : DecideNB(p))
    /\ WF_vars(\E p \in participants : TimeoutAbort(p))
    /\ WF_vars(\E p \in participants : Die(p))

\* No two participants ever reach different decisions.
AC1 ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

\* A commit is only reachable if everybody voted yes.
AC2 ==
    \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

\* An abort is justified by a no vote, a faulty participant, or a faulty coordinator.
AC3 ==
    \A p \in participants : decision[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faulty[q]
        \/ faulty' = [p \in participants |-> TRUE]

\* Decisions, once made, are permanent.
AC4 ==
    \A p \in participants : (decision[p] = commit \/ decision[p] = abort) => [decision EXCEPT ![p] = decision[p]]

\* Every non-faulty participant eventually decides, due to reliable forwarding.
AC5 ==
    \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

Properties == { AC1, AC2, AC3, AC4, AC5 }

====