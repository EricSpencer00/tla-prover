---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, coordState, fwd

vars == <<pstate, alive, decision, faulty, voteSent, coordState, fwd>>

TypeOK ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \subseteq participants
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordState \in [req |-> BOOLEAN, vote |-> {yes, no, undecided},
                    bc |-> [participants -> {commit, abort, waiting}],
                    d |-> {commit, abort, undecided}, alive |-> BOOLEAN,
                    faulty |-> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = {}
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordState = [req |-> FALSE, vote |-> undecided, bc |-> [p \in participants |-> waiting],
                   d |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

DecideCoord ==
  /\ coordState.alive
  /\ coordState.req
  /\ coordState.vote # undecided
  /\ coordState.vote \in {yes, no}
  /\ coordState.d' = IF coordState.vote = yes THEN commit
                       ELSE abort
  /\ coordState.bc' = [p \in participants |-> coordState.d']
  /\ coordState' = [coordState EXCEPT !.req = FALSE]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, fwd>>

SendRequest ==
  /\ coordState.alive
  /\ ~coordState.req
  /\ coordState' = [coordState EXCEPT !.req = TRUE, !.vote = undecided]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, fwd>>

SendVote(p) ==
  /\ coordState.alive
  /\ coordState.req
  /\ p \in participants
  /\ alive[p]
  /\ ~voteSent[p]
  /\ \E v \in {yes, no}: pstate' = [pstate EXCEPT ![p] = v]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordState, fwd>>

DetectFault ==
  /\ coordState.alive
  /\ \E p \in participants: ~alive[p]
  /\ coordState' = [coordState EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, fwd>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ coordState.alive
  /\ coordState.bc[p] # waiting
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordState.bc[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants: q # p /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[CHOOSE q \in participants: q # p /\ fwd[q][p] # notsent][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

Forward(p) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ \E q \in participants:
       /\ p # q
       /\ fwd[p][q] = notsent
       /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] # notsent
  /\ \A q \in participants: q # p => fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, voteSent, coordState, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~coordState.alive
  /\ \A q \in participants: coordState.bc[q] = waiting
  /\ \A q \in participants: \A r \in participants:
       (q \in faulty /\ alive[r]) => fwd[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, voteSent, coordState, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<pstate, decision, voteSent, coordState, fwd>>

DieCoordinator ==
  /\ coordState.alive
  /\ coordState' = [coordState EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, voteSent, fwd>>

Next ==
  \/ DecideCoord \/ SendRequest \/ DetectFault \/ DieCoordinator
  \/ \E p \in participants: SendVote(p) \/ PreDecideFromCoord(p)
                         \/ PreDecideFromFwd(p) \/ Forward(p)
                         \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: SendVote(p))
  /\ WF_vars(\E p \in participants: Forward(p))
  /\ WF_vars(\E p \in participants: Decide(p))
  /\ WF_vars(\E p \in participants: PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants: PreDecideFromFwd(p))
  /\ WF_vars(\E p \in participants: AbortOnTimeout(p))

TypeInvNB == TypeOK

AC1 ==
  \A p, q \in participants: (decision[p] = commit) => (decision[q] # abort)

AC2 ==
  \E p \in participants: decision[p] = commit => \A q \in participants: pstate[q] = yes

AC3 ==
  \E p \in participants: decision[p] = abort =>
    \/ \E q \in participants: pstate[q] = no
    \/ faulty # {}
    \/ coordState.faulty

AC4 ==
  \A p \in participants: (decision[p] # waiting) => (decision[p] = commit \/ decision[p] = abort)

EventualDecision ==
  <>(\A p \in participants: decision[p] # waiting \/ p \in faulty \/ coordState.faulty)

DecideEventually ==
  \A p \in participants: <>(decision[p] # waiting)

====