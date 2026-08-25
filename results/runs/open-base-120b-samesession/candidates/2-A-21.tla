---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no,        \* vote values
    undecided,      \* initial decision value for participants
    commit, abort,  \* final decision values
    waiting,        \* value meaning “no decision yet” (used for broadcasts)
    notsent         \* forwarding status meaning “not yet sent”

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,      \* BOOLEAN – coordinator is alive?
    coordFaulty,     \* BOOLEAN – coordinator is faulty (crashed)?
    coordDecision,  \* {commit, abort, waiting}
    broadcasted,    \* [participants -> {commit, abort, waiting}]
    vote,           \* [participants -> {yes, no}]
    voteSent,       \* [participants -> BOOLEAN]
    alive,          \* [participants -> BOOLEAN]
    faulty,         \* [participants -> BOOLEAN]
    decision,       \* [participants -> {undecided, commit, abort}]
    preDecision,    \* [participants -> {undecided, commit, abort}]
    fwd             \* [participants -> [participants -> {notsent, commit, abort}]]

vars == << coordAlive, coordFaulty, coordDecision, broadcasted,
          vote, voteSent, alive, faulty, decision, preDecision, fwd >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ broadcasted = [p \in participants |-> waiting]
    /\ vote = [p \in participants |-> no]           \* votes are chosen nondeterministically later
    /\ voteSent = [p \in participants |-> FALSE]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ preDecision = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = waiting
    /\ \A p \in participants: voteSent[p]                           \* all votes received
    /\ IF \A p \in participants: vote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << broadcasted, vote, voteSent, alive, faulty,
                    decision, preDecision, fwd >>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # waiting
    /\ broadcasted' = [p \in participants |-> coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, vote,
                    voteSent, alive, faulty, decision, preDecision, fwd >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, broadcasted, vote, voteSent,
                    alive, faulty, decision, preDecision, fwd >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ alive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcasted,
                    vote, alive, faulty, decision, preDecision, fwd >>

PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ preDecision[p] = undecided
    /\ broadcasted[p] # waiting
    /\ preDecision' = [preDecision EXCEPT ![p] = broadcasted[p]]
    /\ fwd' = [fwd EXCEPT ![p][p] = broadcasted[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcasted,
                    vote, voteSent, alive, faulty, decision >>

PreDecideFromFwd(p) ==
    /\ alive[p]
    /\ preDecision[p] = undecided
    /\ \E q \in participants: fwd[q][p] # notsent
    /\ LET d == CHOOSE d \in {commit, abort} :
                \E q \in participants: fwd[q][p] = d IN
       preDecision' = [preDecision EXCEPT ![p] = d]
    /\ fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcasted,
                    vote, voteSent, alive, faulty, decision >>

Forward(p, q) ==
    /\ alive[p]
    /\ preDecision[p] # undecided
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = preDecision[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcasted,
                    vote, voteSent, alive, faulty, decision, preDecision >>

Decide(p) ==
    /\ alive[p]
    /\ preDecision[p] # undecided
    /\ \A q \in participants: q # p => fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = preDecision[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcasted,
                    vote, voteSent, alive, faulty, preDecision, fwd >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants: alive[q] => broadcasted[q] = waiting
    /\ \A q \in participants: ~alive[q] =>
          \A r \in participants: alive[r] => fwd[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcasted,
                    vote, voteSent, alive, faulty, preDecision, fwd >>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcasted,
                    vote, voteSent, decision, preDecision, fwd >>

\* ----------------------------------------------------------------------
\* Disjunction of all possible next-state actions
\* ----------------------------------------------------------------------
Next ==
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants:
          \/ SendVote(p)
          \/ PreDecideFromCoord(p)
          \/ PreDecideFromFwd(p)
          \/ \E q \in participants: q # p /\ Forward(p,q)
          \/ Decide(p)
          \/ AbortOnTimeout(p)
          \/ Die(p)

\* ----------------------------------------------------------------------
\* Fairness assumptions (weak fairness on progress actions, excluding deaths)
\* ----------------------------------------------------------------------
ParticipantProgress ==
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: PreDecideFromCoord(p)
    \/ \E p \in participants: PreDecideFromFwd(p)
    \/ \E p,q \in participants: p # q /\ Forward(p,q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortOnTimeout(p)

CoordinatorProgress ==
    \/ CoordMakeDecision
    \/ CoordBroadcast

SpecNB == Init /\ [][Next]_vars /\ WF_vars(ParticipantProgress) /\ WF_vars(CoordinatorProgress)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, waiting}
    /\ broadcasted \in [participants -> {commit, abort, waiting}]
    /\ vote \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ preDecision \in [participants -> {undecided, commit, abort}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

============================================================================