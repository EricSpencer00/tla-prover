---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants, \* set of participant identifiers
    yes, no,          \* vote values
    undecided, commit, abort,   \* decision values
    waiting,         \* placeholder for coordinator waiting state (unused but required)
    notsent          \* forwarding status indicating no decision sent yet

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* TRUE iff coordinator is alive
    coordFaulty,         \* TRUE iff coordinator has crashed (faulty)
    coordDecision,       \* decision made by coordinator (undecided / commit / abort)
    forwardTable,        \* [p ∈ participants → [q ∈ participants → notsent ∪ {commit, abort}]]
    decisions,           \* [p ∈ participants → undecided ∪ {commit, abort}]
    alive,               \* [p ∈ participants → BOOLEAN]  (TRUE = alive)
    faulty,              \* [p ∈ participants → BOOLEAN]  (TRUE = crashed)
    voteSent,            \* [p ∈ participants → BOOLEAN]  (TRUE = vote already sent)
    votes                \* [p ∈ participants → yes ∪ no] (the vote cast by each participant)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsDecision(d) == d = commit \/ d = abort
AllForwarded(p) == 
    /\ forwardTable[p][p] # notsent
    /\ \A q \in participants : q # p => forwardTable[p][q] = forwardTable[p][p]

AnyForwardedFromCoord(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ forwardTable[p][p] = notsent
    /\ forwardTable[p][p]' = coordDecision

AnyForwardedFromPeer(p) ==
    /\ \E q \in participants : q # p /\ forwardTable[q][p] # notsent
    /\ forwardTable[p][p] = notsent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]
    /\ decisions    = [p \in participants |-> undecided]
    /\ alive        = [p \in participants |-> TRUE]
    /\ faulty       = [p \in participants |-> FALSE]
    /\ voteSent     = [p \in participants |-> FALSE]
    /\ votes        = [p \in participants |-> no]   \* initial vote (may be changed later)

\* ----------------------------------------------------------------------
\* Coordinator actions (simplified, reusing base protocol ideas)
\* ----------------------------------------------------------------------
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, forwardTable, decisions, alive, faulty, voteSent, votes>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : votes[p] = yes   \* all votes yes
    /\ coordDecision' = commit
    /\ UNCHANGED <<coordAlive, forwardTable, decisions, alive, faulty, voteSent, votes>>

CoordMakeDecisionAbort ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \E p \in participants : votes[p] = no
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, forwardTable, decisions, alive, faulty, voteSent, votes>>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants : alive[p] /\ forwardTable[p][p] = notsent
    /\ \A p \in participants :
          IF alive[p] THEN
              forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
          ELSE UNCHANGED forwardTable
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, decisions, alive, faulty, voteSent, votes>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, forwardTable, decisions, alive, faulty, votes>>

ParticipantPreDecideFromCoord(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwardTable[p][p] = notsent
    /\ coordAlive
    /\ coordDecision # undecided
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, decisions, alive, faulty, voteSent, votes>>

ParticipantPreDecideFromPeer(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwardTable[p][p] = notsent
    /\ \E q \in participants : q # p /\ forwardTable[q][p] # notsent
    /\ LET d == CHOOSE d \in {commit, abort} : 
                \E q \in participants : q # p /\ forwardTable[q][p] = d
       IN forwardTable' = [forwardTable EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, decisions, alive, faulty, voteSent, votes>>

ParticipantForward(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwardTable[p][p] # notsent
    /\ \E q \in participants : q # p /\ forwardTable[p][q] = notsent
    /\ LET q == CHOOSE q \in participants : q # p /\ forwardTable[p][q] = notsent
          d == forwardTable[p][p]
       IN forwardTable' = [forwardTable EXCEPT ![p][q] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, decisions, alive, faulty, voteSent, votes>>

ParticipantDecide(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwardTable[p][p] # notsent
    /\ AllForwarded(p)
    /\ decisions' = [decisions EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, forwardTable, alive, faulty, voteSent, votes>>

ParticipantAbortTimeout(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ decisions[p] = undecided
    /\ (coordFaulty \/ ~coordAlive)
    /\ \A q \in participants : 
          (alive[q] => forwardTable[q][q] = notsent)
    /\ \A q \in participants : 
          (faulty[q] => \A r \in participants : forwardTable[q][r] = notsent)
    /\ decisions' = [decisions EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, forwardTable, alive, faulty, voteSent, votes>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, forwardTable, decisions, voteSent, votes>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ \E p \in participants : ParticipantPreDecideFromCoord(p)
    \/ \E p \in participants : ParticipantPreDecideFromPeer(p)
    \/ \E p \in participants : ParticipantForward(p)
    \/ \E p \in participants : ParticipantDecide(p)
    \/ \E p \in participants : ParticipantAbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordMakeDecision
    \/ CoordMakeDecisionAbort
    \/ CoordBroadcast
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                     forwardTable, decisions, alive, faulty,
                     voteSent, votes>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ decisions \in [participants -> {undecided, commit, abort}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ votes \in [participants -> {yes, no}]

\* ----------------------------------------------------------------------
\* Safety properties (expressed as invariants)
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (decisions[p] = commit /\ decisions[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants :
        decisions[p] = commit => \A q \in participants : votes[q] = yes

AbortValidity ==
    \A p \in participants :
        decisions[p] = abort => 
            (\E q \in participants : votes[q] = no) \/ (\E q \in participants : faulty[q]) \/ coordFaulty

Irrevocability ==
    \A p \in participants :
        (decisions[p] = commit \/ decisions[p] = abort) => 
            [] (decisions[p] = commit \/ decisions[p] = abort)

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
AC3Liveness == 
    <> ( \A p \in participants : decisions[p] # undecided
        \/ \E p \in participants : faulty[p]
        \/ coordFaulty)

NonBlockingTermination ==
    \A p \in participants :
        (alive[p] /\ ~faulty[p]) => <> (decisions[p] # undecided)

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====