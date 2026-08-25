---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants, \* the set of participant identifiers
    yes, no,        \* vote values
    undecided, commit, abort, waiting, \* decision values
    notsent         \* forwarding status when nothing has been sent

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLES
    coordAlive,          \* BOOLEAN – coordinator is up
    coordFaulty,         \* BOOLEAN – coordinator has crashed
    coordDecision,       \* {waiting, commit, abort}
    votes,               \* [participants -> {yes,no}]
    decs,                \* [participants -> {undecided, commit, abort}]
    forward,             \* [participants -> [participants -> {notsent, commit, abort}]]
    alive,               \* SUBSET participants – participants that are up
    faulty               \* SUBSET participants – participants that have crashed

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
\* The set of all variables for the stuttering operator
vars == << coordAlive, coordFaulty, coordDecision,
           votes, decs, forward, alive, faulty >>

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ votes = [p \in participants |-> yes]    \* arbitrary initial vote
    /\ decs = [p \in participants |-> undecided]
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]
    /\ alive = participants
    /\ faulty = {}

\* -----------------------------------------------------------------
\* Coordinator actions
\* -----------------------------------------------------------------
\* The coordinator decides (commit if all votes are yes, abort otherwise)
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = waiting
    /\ IF \A p \in participants: votes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordFaulty, votes, decs, forward, alive, faulty>>

\* The coordinator broadcasts its decision to every participant
CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ forward' = [p \in participants |-> [q \in participants |-> 
                     IF q = p THEN coordDecision ELSE forward[p][q]]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, decs, alive, faulty>>

\* The coordinator crashes (becomes faulty)
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, votes, decs, forward, alive, faulty>>

\* -----------------------------------------------------------------
\* Participant actions
\* -----------------------------------------------------------------
\* A participant sends its vote (nondeterministically yes or no)
SendVote(p) ==
    /\ p \in alive
    /\ \E v \in {yes, no}:
          /\ votes' = [votes EXCEPT ![p] = v]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         decs, forward, alive, faulty>>

\* Pre‑decide from the coordinator (first receipt of the decision)
PreDecideFromCoord(p) ==
    /\ p \in alive
    /\ forward[p][p] = notsent
    /\ coordDecision \in {commit, abort}
    /\ forward' = [forward EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                  decs, alive, faulty>>

\* Pre‑decide from another participant that has already forwarded
PreDecideFromFwd(p,q) ==
    /\ p \in alive
    /\ q \in participants
    /\ forward[p][p] = notsent
    /\ forward[q][p] # notsent
    /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                  decs, alive, faulty>>

\* Forward the pre‑decision to another participant
Forward(p,q) ==
    /\ p \in alive
    /\ q \in participants
    /\ forward[p][p] \in {commit, abort}
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                  decs, alive, faulty>>

\* Decide locally after having forwarded to everyone
Decide(p) ==
    /\ p \in alive
    /\ forward[p][p] \in {commit, abort}
    /\ \A q \in participants: forward[p][q] # notsent
    /\ decs[p] = undecided
    /\ decs' = [decs EXCEPT ![p] = forward[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                  forward, alive, faulty>>

\* Abort because of timeout (coordinator dead and no decision reachable)
AbortTimeout(p) ==
    /\ p \in alive
    /\ decs[p] = undecided
    /\ \/ coordAlive = FALSE
       \/ coordFaulty = TRUE
    /\ \A q \in participants: forward[q][p] = notsent
    /\ decs' = [decs EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, forward, alive, faulty>>

\* Participant crashes
ParticipantDie(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, decs, forward>>

\* -----------------------------------------------------------------
\* The Next-state relation
\* -----------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVote(p)
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants: PreDecideFromCoord(p)
    \/ \E p,q \in participants: PreDecideFromFwd(p,q)
    \/ \E p,q \in participants: Forward(p,q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortTimeout(p)
    \/ \E p \in participants: ParticipantDie(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* -----------------------------------------------------------------
\* Type invariant (used for model checking)
\* -----------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {waiting, commit, abort}
    /\ votes \in [participants -> {yes, no}]
    /\ decs \in [participants -> {undecided, commit, abort}]
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ alive \subseteq participants
    /\ faulty \subseteq participants
    /\ disjoint alive, faulty

\* -----------------------------------------------------------------
\* End of module
\* -----------------------------------------------------------------
====