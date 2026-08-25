---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  participants, \* set of participant identifiers
  yes, no,          \* possible votes
  undecided, commit, abort, \* decision values
  waiting,          \* coordinator request state (unused but required)
  notsent           \* forwarding status for “no decision yet”

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
  coordAlive,        \* TRUE iff the coordinator is alive
  coordFaulty,       \* TRUE iff the coordinator has crashed
  coordDecision,    \* {undecided, commit, abort}
  alive,            \* subset of participants that are alive
  faulty,           \* subset of participants that have crashed
  vote,             \* [participants -> {yes,no,undecided}]
  voteSent,         \* [participants -> BOOLEAN]
  decision,         \* [participants -> {undecided, commit, abort}]
  forwarding        \* [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ alive = participants
  /\ faulty = {}
  /\ vote = [p \in participants |-> undecided]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ decision = [p \in participants |-> undecided]
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Participant actions
Vote(p) ==
  /\ p \in alive
  /\ voteSent[p] = FALSE
  /\ \E v \in {yes, no}:
        /\ vote' = [vote EXCEPT ![p] = v]
        /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                        alive, faulty, decision, forwarding >>
        
AbortOnVote(p) ==
  /\ p \in alive
  /\ vote[p] = no
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                  alive, faulty, vote, voteSent, forwarding >>

PreDecideFromCoordinator(p) ==
  /\ p \in alive
  /\ forwarding[p][p] = notsent
  /\ coordAlive = TRUE
  /\ coordDecision # undecided
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                  alive, faulty, vote, voteSent, decision >>

PreDecideFromForward(p, q) ==
  /\ p \in alive
  /\ q \in alive
  /\ forwarding[p][p] = notsent
  /\ forwarding[q][p] # notsent
  /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                  alive, faulty, vote, voteSent, decision >>

Forward(p, q) ==
  /\ p \in alive
  /\ q \in participants
  /\ forwarding[p][p] # notsent
  /\ forwarding[p][q] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                  alive, faulty, vote, voteSent, decision >>

Decide(p) ==
  /\ p \in alive
  /\ \A q \in participants: forwarding[p][q] # notsent
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                  alive, faulty, vote, voteSent, forwarding >>

AbortOnTimeout(p) ==
  /\ p \in alive
  /\ decision[p] = undecided
  /\ coordAlive = FALSE
  /\ \A q \in participants: forwarding[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                  alive, faulty, vote, voteSent, forwarding >>

DieParticipant(p) ==
  /\ p \in alive
  /\ alive' = alive \ {p}
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                  vote, voteSent, decision, forwarding >>

\* ----------------------------------------------------------------------
\* Coordinator actions
CoordMakeDecision ==
  /\ coordAlive = TRUE
  /\ coordDecision = undecided
  /\ \A p \in participants: voteSent[p] = TRUE
  /\ IF \A p \in participants: vote[p] = yes
        THEN coordDecision' = commit
        ELSE coordDecision' = abort
  /\ UNCHANGED << coordAlive, coordFaulty, alive, faulty,
                  vote, voteSent, decision, forwarding >>

CoordinatorDie ==
  /\ coordAlive = TRUE
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << alive, faulty, vote, voteSent, decision, forwarding,
                  coordDecision >>

\* ----------------------------------------------------------------------
\* Combined next-state relation
Next ==
  \/ \E p \in participants: Vote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: PreDecideFromCoordinator(p)
  \/ \E p \in participants: \E q \in participants: PreDecideFromForward(p, q)
  \/ \E p \in participants: \E q \in participants: Forward(p, q)
  \/ \E p \in participants: Decide(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: DieParticipant(p)
  \/ CoordinatorDie
  \/ CoordMakeDecision

\* ----------------------------------------------------------------------
\* Temporal specification
vars == << coordAlive, coordFaulty, coordDecision,
           alive, faulty, vote, voteSent, decision, forwarding >>

SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvNB ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ alive \subseteq participants
  /\ faulty \subseteq participants
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

====