---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, coordState, forward
vars == <<vote, alive, decision, faulty, voteSent, coordState, forward>>

\* Forwarding table: forward[p][q] tracks participant p's forwarding history
\* towards participant q (not-sent, commit, or abort). The coordinator logic
\* (request, vote, broadcast, decision) is inherited unchanged from ACP-SB.
InitPart == [alive |-> TRUE, decision |-> undecided, voteSent |-> FALSE]
InitCoord == [request |-> waiting, vote |-> undecided, broadcast |-> undecided,
              decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]

TypeInv ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordState \in [request : {waiting, yes, no},
                     vote : {yes, no, undecided},
                     broadcast : {commit, abort, notsent},
                     decision : {commit, abort, undecided},
                     alive : BOOLEAN, faulty : BOOLEAN]
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordState = InitCoord
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordState.alive
  /\ coordState.request = waiting
  /\ coordState' = [coordState EXCEPT !.request = yes]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, forward>>

GetVote(p) ==
  /\ coordState.alive
  /\ coordState.request # waiting
  /\ coordState.vote = undecided
  /\ voteSent[p] = FALSE
  /\ vote[p] # undecided
  /\ coordState' = [coordState EXCEPT !.vote = vote[p]]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, forward>>

DetectFault ==
  /\ coordState.alive
  /\ coordState.request = yes
  /\ coordState.vote = undecided
  /\ \E p \in participants : ~alive[p]
  /\ coordState' = [coordState EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<vote, alive, decision, voteSent, faulty, forward>>

MakeDecision ==
  /\ coordState.alive
  /\ coordState.request # waiting
  /\ coordState.vote # undecided
  /\ coordState.decision = undecided
  /\ coordState' = [coordState EXCEPT !.decision = coordState.vote]
  /\ UNCHANGED <<vote, alive, decision, voteSent, faulty, forward>>

Broadcast(p) ==
  /\ coordState.alive
  /\ coordState.broadcast = notsent
  /\ coordState.decision # undecided
  /\ alive[p]
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = coordState.decision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordState>>

Decide(p) ==
  /\ decision[p] = undecided
  /\ \E q \in participants : forward[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, voteSent, faulty, coordState, forward>>

SendVote(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, coordState, forward>>

AbortFromCoordinator(p) ==
  /\ alive[p]
  /\ coordState.alive
  /\ coordState.broadcast # notsent
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = coordState.broadcast]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordState>>

AbortFromForwarding(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] = notsent
  /\ \E q \in participants :
       /\ forward[q][p] # notsent
       /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordState>>

Forward(p) ==
  /\ alive[p]
  /\ forward[p][p] # notsent
  /\ \E q \in participants :
       /\ forward[p][q] = notsent
       /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, voteSent, coordState>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordState.alive
  /\ \A q \in participants : forward[q][p] = notsent
  /\ \A q \in participants : (coordState.alive => coordState.broadcast = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, voteSent, faulty, coordState, forward>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, voteSent, coordState, forward>>

Next ==
  \/ SendRequest \/ DetectFault \/ MakeDecision
  \/ \E p \in participants : GetVote(p) \/ Broadcast(p) \/ Decide(p) \/ SendVote(p)
  \/ \E p \in participants : AbortFromCoordinator(p) \/ AbortFromForwarding(p)
  \/ \E p \in participants : Forward(p) \/ AbortOnTimeout(p) \/ Die(p)

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(SendRequest) /\ WF_vars(DetectFault) /\ WF_vars(MakeDecision)
  /\ \A p \in participants :
       WF_vars(GetVote(p)) /\ WF_vars(Decide(p)) /\ WF_vars(SendVote(p))
       /\ WF_vars(AbortFromCoordinator(p)) /\ WF_vars(AbortFromForwarding(p))
       /\ WF_vars(Forward(p)) /\ WF_vars(AbortOnTimeout(p))

\* Safety: agreement and validity properties, inherited from ACP-SB.
Agreed == ~(decision[a] = commit /\ decision[b] = abort)
ValidCommit == decision[a] = commit => vote[a] = yes
ValidAbort == decision[a] = abort => (vote[a] = no \/ a \in faulty \/ coordState.faulty)
Irreversible == \A p \in participants : (decision[p] # undecided) ~> (decision[p] # undecided)

\* Liveness: eventual decision of the whole set (AC3), and non-blocking
\* termination of every non-faulty participant (AC5, new for ACP-NB).
EventualDecision ==
  \E Q \in {{commit, abort}, {aborted}, {commit}} : <>(decision = Q \/ faulty # {} \/ coordState.faulty)
Termination == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

TypeInvNB == TypeInv
SAFETY == Agreed /\ ValidCommit /\ ValidAbort /\ Irreversible
AC3 == EventualDecision
AC5 == Termination
====