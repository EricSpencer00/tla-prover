---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants,   \* set of participant identifiers
    yes, no,        \* vote values
    undecided, commit, abort, waiting, notsent   \* decision/status values

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* TRUE iff the coordinator is alive
    coordFaulty,         \* TRUE iff the coordinator has crashed
    coordDecision,       \* decision made by the coordinator (undecided, commit, abort)
    coordSent,           \* [participants -> BOOLEAN]  whether coord has broadcast to each p
    votes,               \* [participants -> {yes,no}]  vote cast by each participant
    voteSent,            \* [participants -> BOOLEAN]  whether the vote has been sent
    participantAlive,    \* [participants -> BOOLEAN]  alive status of each participant
    participantFaulty,   \* [participants -> BOOLEAN]  faulty flag of each participant
    participantDecision, \* [participants -> {undecided, commit, abort}]  final decision
    forwarding           \* [participants -> [participants -> {notsent, commit, abort}]]
    
\* ----------------------------------------------------------------------
\* Helper sets
\* ----------------------------------------------------------------------
VoteValues == {yes, no}
DecisionVals == {commit, abort, undecided}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSent = [p \in participants |-> FALSE]
    /\ votes = [p \in participants |-> yes]          \* placeholder; actual vote set when sent
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ ~voteSent[p]
    /\ votes' = [votes EXCEPT ![p] = CHOOSE v \in VoteValues: TRUE]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  participantAlive, participantFaulty,
                  participantDecision, forwarding>>

PreDecideFromCoordinator(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordDecision \in {commit, abort}
    /\ coordSent[p]
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  votes, voteSent, participantAlive, participantFaulty,
                  participantDecision>>

PreDecideFromForward(p,q) ==
    /\ p \in participants /\ q \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ forwarding[q][p] \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  votes, voteSent, participantAlive, participantFaulty,
                  participantDecision>>

Forward(p,q) ==
    /\ p \in participants /\ q \in participants
    /\ participantAlive[p]
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  votes, voteSent, participantAlive, participantFaulty,
                  participantDecision>>

Decide(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ \A q \in participants: forwarding[p][q] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  votes, voteSent, participantAlive, participantFaulty,
                  forwarding>>

AbortTimeout(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ \A a \in participants: participantAlive[a] => forwarding[a][a] = notsent
    /\ \A a \in participants: ~participantAlive[a] => 
          \A b \in participants: participantAlive[b] => forwarding[a][b] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  votes, voteSent, participantAlive, participantFaulty,
                  forwarding>>

Die(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  votes, voteSent, participantDecision, forwarding>>

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordinatorMakeDecision ==
    /\ coordAlive
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED <<coordFaulty, coordSent, votes, voteSent,
                  participantAlive, participantFaulty,
                  participantDecision, forwarding>>

CoordinatorBroadcast(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ coordSent' = [coordSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  votes, voteSent, participantAlive, participantFaulty,
                  participantDecision, forwarding>>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordSent, votes, voteSent,
                  participantAlive, participantFaulty,
                  participantDecision, forwarding>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: PreDecideFromCoordinator(p)
    \/ \E p \in participants: \E q \in participants: PreDecideFromForward(p,q)
    \/ \E p \in participants: \E q \in participants: Forward(p,q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortTimeout(p)
    \/ \E p \in participants: Die(p)
    \/ CoordinatorMakeDecision
    \/ \E p \in participants: CoordinatorBroadcast(p)
    \/ CoordinatorDie

\* ----------------------------------------------------------------------
\* Variables tuple for temporal operators
\* ----------------------------------------------------------------------
vars == <<coordAlive, coordFaulty, coordDecision, coordSent,
          votes, voteSent, participantAlive, participantFaulty,
          participantDecision, forwarding>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in DecisionVals
    /\ coordSent \in [participants -> BOOLEAN]
    /\ votes \in [participants -> VoteValues]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

====