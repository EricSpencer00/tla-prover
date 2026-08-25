---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS
    participants,   \* the set of participant identifiers
    yes, no,         \* vote values
    undecided, commit, abort, \* participant decision values
    waiting,        \* vote not yet cast
    notsent         \* forwarding table entry meaning “no decision forwarded yet”

\* --------------------------------------------------------------
\* State variables
\* --------------------------------------------------------------
VARIABLES
    coordAlive,          \* BOOLEAN, TRUE iff the coordinator is alive
    coordFaulty,         \* BOOLEAN, TRUE iff the coordinator has crashed
    coordDecision,       \* {commit, abort} ∪ {None}, the decision made by the coordinator
    coordBroadcasted,    \* [participants -> BOOLEAN], which participants have already been sent the decision by the coordinator
    votes,               \* [participants -> {yes, no, waiting}]
    decision,            \* [participants -> {undecided, commit, abort}]
    fwd                  \* [participants -> [participants -> {notsent, commit, abort}]]

\* --------------------------------------------------------------
\* Type invariant
\* --------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort} \cup {None}
    /\ coordBroadcasted \in [participants -> BOOLEAN]
    /\ votes \in [participants -> {yes, no, waiting}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = None
    /\ coordBroadcasted = [p \in participants |-> FALSE]
    /\ votes = [p \in participants |-> waiting]
    /\ decision = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* --------------------------------------------------------------
\* Coordinator actions
\* --------------------------------------------------------------

\* The coordinator may cast a vote (once it has collected all votes)
\* For simplicity we allow the coordinator to decide nondeterministically
\* when all participants have voted.
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = None
    /\ \A p \in participants : votes[p] # waiting
    /\ \* commit only if all votes are yes; otherwise abort
       IF \A p \in participants : votes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, votes, decision, fwd, coordBroadcasted>>

\* The coordinator sends its decision to a single (still alive) participant.
CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # None
    /\ \E p \in participants :
          /\ ~coordBroadcasted[p]
          /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, decision, fwd>>

\* The coordinator crashes.
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcasted, votes, decision, fwd>>

\* --------------------------------------------------------------
\* Participant actions
\* --------------------------------------------------------------

\* A participant casts its vote (yes or no) when still waiting.
ParticipantVote ==
    /\ \E p \in participants :
          /\ votes[p] = waiting
          /\ votes' = [votes EXCEPT ![p] = 
                IF BOOLEAN THEN yes ELSE no]   \* nondeterministic choice
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted, decision, fwd>>

\* Pre‑decide from coordinator broadcast.
PreDecideFromCoord ==
    /\ \E p \in participants :
          /\ coordAlive
          /\ coordDecision # None
          /\ coordBroadcasted[p]
          /\ fwd[p][p] = notsent
          /\ fwd' = [fwd EXCEPT ![p][p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted, votes, decision>>

\* Pre‑decide from another participant's forwarding.
PreDecideFromForward ==
    /\ \E p,q \in participants :
          /\ p # q
          /\ fwd[p][p] = notsent
          /\ fwd[q][p] # notsent
          /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted, votes, decision>>

\* Forward a pre‑decision to another participant.
Forward ==
    /\ \E p,r \in participants :
          /\ fwd[p][p] # notsent               \* p has a pre‑decision
          /\ fwd[p][r] = notsent               \* not yet forwarded to r
          /\ fwd' = [fwd EXCEPT ![p][r] = fwd[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted, votes, decision>>

\* Decide once the pre‑decision has been forwarded to everyone.
Decide ==
    /\ \E p \in participants :
          /\ fwd[p][p] # notsent
          /\ \A r \in participants : fwd[p][r] # notsent
          /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted, votes, fwd>>

\* Abort on timeout when the coordinator is dead and no decision can be learned.
AbortOnTimeout ==
    /\ \E p \in participants :
          /\ decision[p] = undecided
          /\ coordAlive = FALSE
          /\ \A q \in participants :
                (coordBroadcasted[q] = FALSE)          \* coordinator never reached q
                \/ (coordBroadcasted[q] = TRUE /\ decision[q] = undecided)   \* alive participants still undecided
          /\ \A d \in participants :
                (coordAlive = FALSE) => 
                (\A r \in participants :
                     fwd[d][r] = notsent)               \* dead participants have forwarded nothing
          /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted, votes, fwd>>

\* Participant crashes.
ParticipantDie ==
    /\ \E p \in participants :
          /\ coordAlive = TRUE      \* crash does not depend on coordinator state
          /\ decision[p] = undecided
          /\ decision' = [decision EXCEPT ![p] = undecided]   \* decision stays undecided
          /\ fwd' = [fwd EXCEPT ![p] = [q \in participants |-> notsent]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted, votes>>

\* --------------------------------------------------------------
\* Next-state relation
\* --------------------------------------------------------------
Next ==
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ ParticipantVote
    \/ PreDecideFromCoord
    \/ PreDecideFromForward
    \/ Forward
    \/ Decide
    \/ AbortOnTimeout
    \/ ParticipantDie

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
vars == <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
          votes, decision, fwd>>

SpecNB == Init /\ [][Next]_vars

\* --------------------------------------------------------------
\* Invariants
\* --------------------------------------------------------------
\* TypeInvNB already defined above.
\* Additional safety invariants (agreement, irrevocability, etc.) could be
\* added here, but only TypeInvNB is required by the configuration.

====