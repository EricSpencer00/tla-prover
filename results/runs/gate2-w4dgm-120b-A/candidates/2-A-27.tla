---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Inherited state from ACP-SB (the base simple broadcast protocol); 'forw'
\* is the per-participant forwarding table for reliable broadcast.
VARIABLES pstate, alive, decision, faulty, sentVote, coordState, forw

vars == << pstate, alive, decision, faulty, sentVote, coordState, forw >>

Bump(x) == IF x = undecided THEN waiting ELSE x

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordState = [req |-> undecided, vote |-> undecided, sent |-> FALSE,
                   dec |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ forw = [p \in participants |-> [q \in participants |-> notsent]]

Request ==
  /\ coordState.alive
  /\ coordState.req = undecided
  /\ coordState' = [coordState EXCEPT !.req = waiting]
  /\ UNCHANGED << pstate, alive, decision, faulty, sentVote, forw >>

CastVote(p) ==
  /\ coordState.alive
  /\ alive[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ coordState' = [coordState EXCEPT !.vote = Bump(coordState.vote)]
  /\ UNCHANGED << pstate, alive, decision, faulty, forw >>

DetectCoordFault ==
  /\ coordState.alive
  /\ coordState.alive' = FALSE
  /\ coordState' = [coordState EXCEPT !.faulty = TRUE]
  /\ UNCHANGED << pstate, alive, decision, faulty, sentVote, forw >>

DecideCoord ==
  /\ coordState.alive
  /\ coordState.req = waiting
  /\ coordState.vote # undecided
  /\ coordState.sent = FALSE
  /\ coordState.dec' = IF coordState.vote = waiting THEN abort ELSE commit
  /\ coordState.sent' = TRUE
  /\ UNCHANGED << pstate, alive, decision, faulty, sentVote, forw >>

BroadcastCoord(p) ==
  /\ coordState.alive
  /\ coordState.sent
  /\ coordState.dec # undecided
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = coordState.dec]
  /\ UNCHANGED << pstate, alive, faulty, sentVote, coordState, forw >>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pstate, decision, sentVote, coordState, forw >>

\* Reliable broadcast: a pre-decision may be received either from the
\* coordinator or from any other participant's forwarding entry.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ forw[p][p] = notsent
  /\ decision[p] # undecided
  /\ forw' = [forw EXCEPT ![p][p] = decision[p]]
  /\ UNCHANGED << pstate, alive, decision, faulty, sentVote, coordState >>

PreDecideForw(p) ==
  /\ alive[p]
  /\ forw[p][p] = notsent
  /\ \E q \in participants : q # p /\ forw[q][p] # notsent
  /\ forw' = [forw EXCEPT ![p][p] = CHOOSE q \in participants :
                            q # p /\ forw[q][p] # notsent
                            /\ forw[q][p]]
  /\ UNCHANGED << pstate, alive, decision, faulty, sentVote, coordState >>

Forward(p, q) ==
  /\ alive[p]
  /\ forw[p][p] # notsent
  /\ forw[p][q] = notsent
  /\ forw' = [forw EXCEPT ![p][q] = forw[p][p]]
  /\ UNCHANGED << pstate, alive, decision, faulty, sentVote, coordState >>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forw[p][p] # notsent
  /\ \A q \in participants \ {p} : forw[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forw[p][p]]
  /\ UNCHANGED << pstate, alive, faulty, sentVote, coordState, forw >>

Abort(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordState.alive
  /\ (\A q \in participants : ~coordState.sent \/ decision[q] = undecided)
  /\ (\A q \in participants : ~alive[q] \/ forw[q][p] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << pstate, alive, faulty, sentVote, coordState, forw >>

Next ==
  \/ Request
  \/ DetectCoordFault
  \/ DecideCoord
  \/ \E p \in participants : CastVote(p) \/ BroadcastCoord(p) \/ Die(p)
                           \/ PreDecideCoord(p) \/ PreDecideForw(p)
                           \/ Decide(p) \/ Abort(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : CastVote(p))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))

TypeInvNB ==
  /\ pstate \in [participants -> {undecided, waiting}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordState \in [req : {undecided, waiting},
                     vote : {undecided, waiting},
                     sent : BOOLEAN, dec : {undecided, commit, abort},
                     alive : BOOLEAN, faulty : BOOLEAN]
  /\ forw \in [participants -> [participants -> {notsent, commit, abort}]]

\* With reliable broadcast, every non-faulty participant eventually decides:
Terminate == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====