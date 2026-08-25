---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE iff the coordinator is alive
    coordFaulty,         \* TRUE iff the coordinator is faulty (crashed)
    coordDecision,       \* {commit, abort, undecided} – decision made by coordinator
    coordBroadcasted,    \* [participants -> BOOLEAN] – whether a participant has
                         \*   received the broadcast from the coordinator
    votes,               \* [participants -> {yes, no, NULL}] – votes sent to coordinator
    alive,               \* [participants -> BOOLEAN] – participant liveness
    faulty,              \* [participants -> BOOLEAN] – participant fault flag
    decision,            \* [participants -> {undecided, commit, abort}] – final decision
    preDecision,         \* [participants -> {undecided, commit, abort}] – pre‑decision stored
    forwardTable         \* [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NULL == "NULL"

\* The set of all variables for the stuttering operator
vars == <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
          votes, alive, faulty, decision, preDecision, forwardTable>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcasted = [p \in participants |-> FALSE]
    /\ votes = [p \in participants |-> NULL]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ preDecision = [p \in participants |-> undecided]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
\* (1) Make a decision after collecting votes (simplified: nondeterministic)
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \E d \in {commit, abort} :
          /\ coordDecision' = d
          /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcasted,
                         votes, alive, faulty, decision,
                         preDecision, forwardTable>>

\* (2) Broadcast the decision to a single participant (one step per participant)
CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants :
          /\ ~coordBroadcasted[p]
          /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         votes, alive, faulty, decision,
                         preDecision, forwardTable>>

\* (3) Coordinator crashes
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcasted,
                   votes, alive, faulty, decision,
                   preDecision, forwardTable>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* (a) Send a vote (yes or no) to the coordinator
ParticipantSendVote ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ ~faulty[p]
          /\ votes[p] = NULL
          /\ \E v \in {yes, no} :
                /\ votes' = [votes EXCEPT ![p] = v]
                /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                               coordBroadcasted, alive, faulty,
                               decision, preDecision, forwardTable>>

\* (b) Receive pre‑decision directly from the coordinator
PreDecideFromCoord ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ preDecision[p] = undecided
          /\ coordDecision # undecided
          /\ coordBroadcasted[p]   \* coordinator has broadcast to p
          /\ preDecision' = [preDecision EXCEPT ![p] = coordDecision]
          /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         coordBroadcasted, votes, alive, faulty,
                         decision>>

\* (c) Receive pre‑decision forwarded by another participant
PreDecideFromForward ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ preDecision[p] = undecided
          /\ \E q \in participants :
                /\ q # p
                /\ forwardTable[q][p] \in {commit, abort}
                /\ LET d == forwardTable[q][p] IN
                     /\ preDecision' = [preDecision EXCEPT ![p] = d]
                     /\ forwardTable' = [forwardTable EXCEPT ![p][p] = d]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         coordBroadcasted, votes, alive, faulty,
                         decision>>

\* (d) Forward the stored pre‑decision to a specific participant
Forward ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ preDecision[p] # undecided
          /\ \E r \in participants :
                /\ r # p
                /\ forwardTable[p][r] = notsent
                /\ forwardTable' = [forwardTable EXCEPT ![p][r] = preDecision[p]]
                /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                               coordBroadcasted, votes, alive, faulty,
                               decision, preDecision, preDecision>>

\* (e) Decide locally after having forwarded to everyone
Decide ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ preDecision[p] # undecided
          /\ \A r \in participants : forwardTable[p][r] # notsent
          /\ decision' = [decision EXCEPT ![p] = preDecision[p]]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         coordBroadcasted, votes, alive, faulty,
                         preDecision, forwardTable>>

\* (f) Abort on timeout when coordinator is dead and no decision can be learned
AbortTimeout ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ decision[p] = undecided
          /\ coordAlive = FALSE
          /\ \A q \in participants : ~coordBroadcasted[q]   \* no broadcast received
          /\ \A q \in participants :
                /\ ~alive[q]   \* dead participant
                /\ \A r \in participants :
                      /\ alive[r] => forwardTable[q][r] = notsent
          /\ decision' = [decision EXCEPT ![p] = abort]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         coordBroadcasted, votes, alive, faulty,
                         preDecision, forwardTable>>

\* (g) Participant crashes
ParticipantDie ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ alive' = [alive EXCEPT ![p] = FALSE]
          /\ faulty' = [faulty EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         coordBroadcasted, votes, decision,
                         preDecision, forwardTable>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ ParticipantSendVote
    \/ PreDecideFromCoord
    \/ PreDecideFromForward
    \/ Forward
    \/ Decide
    \/ AbortTimeout
    \/ ParticipantDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordBroadcasted \in [participants -> BOOLEAN]
    /\ votes \in [participants -> {yes, no, NULL}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ preDecision \in [participants -> {undecided, commit, abort}]
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====