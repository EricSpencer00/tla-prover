---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS 
    participants, \* set of participant identifiers
    yes, no,               \* vote values
    undecided, commit, abort, \* decision values
    waiting,               \* auxiliary constant (unused but required)
    notsent                \* forwarding status

\* ----------------------------------------------------------------------
\* State variables
VARIABLES 
    coordAlive,            \* TRUE when coordinator is alive
    coordFaulty,           \* TRUE when coordinator has crashed
    coordDecision,         \* coordinator's decision (undecided/commit/abort)
    coordBroadcast,        \* [p \in participants -> BOOLEAN], whether the coordinator has sent the decision to p
    voteSent,              \* SUBSET participants that have already sent their vote
    voteVal,               \* [p \in participants -> {yes,no}], vote value of participants that have voted
    decision,              \* [p \in participants -> {undecided,commit,abort}], final decision of each participant
    alive,                 \* SUBSET participants that are currently alive
    faulty,                \* SUBSET participants that have crashed
    pre,                   \* [p \in participants -> {notsent,commit,abort}], own pre‑decision entry (forwarding table diagonal)
    forward                \* [p \in participants -> [q \in participants -> {notsent,commit,abort}]], forwarding status

\* ----------------------------------------------------------------------
\* Helper definitions
vars == <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
          voteSent, voteVal, decision, alive, faulty, pre, forward>>

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcast = [p \in participants |-> FALSE]
    /\ voteSent = {}
    /\ voteVal = [p \in participants |-> yes]            \* default, value used only after p \in voteSent
    /\ decision = [p \in participants |-> undecided]
    /\ alive = participants
    /\ faulty = {}
    /\ pre = [p \in participants |-> notsent]
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
CoordMakeDecision ==
    /\ coordAlive
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ \A p \in participants :
          (p \in voteSent) => voteVal[p] = yes
    /\ coordDecision' = IF \E p \in participants : (p \in voteSent) /\ voteVal[p] = no
                         THEN abort
                         ELSE commit
    /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcast,
                   voteSent, voteVal, decision, alive, faulty, pre, forward>>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants :
          /\ coordBroadcast[p] = FALSE
          /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         voteSent, voteVal, decision, alive, faulty, pre, forward>>
    /\ TRUE

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcast, voteSent, voteVal,
                   decision, alive, faulty, pre, forward>>

\* ----------------------------------------------------------------------
\* Participant actions
ParticipantSendVote ==
    /\ \E p \in alive :
          /\ p \notin voteSent
          /\ LET v == IF Random() % 2 = 0 THEN yes ELSE no IN
                /\ voteSent' = voteSent \cup {p}
                /\ voteVal' = [voteVal EXCEPT ![p] = v]
                /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                               decision, alive, faulty, pre, forward>>
    /\ TRUE

PreDecideFromCoord ==
    /\ \E p \in alive :
          /\ pre[p] = notsent
          /\ coordBroadcast[p] = TRUE
          /\ pre' = [pre EXCEPT ![p] = coordDecision]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                         voteSent, voteVal, decision, alive, faulty, forward>>

PreDecideFromForward ==
    /\ \E p \in alive :
          /\ pre[p] = notsent
          /\ \E q \in participants :
                /\ forward[q][p] # notsent
                /\ pre' = [pre EXCEPT ![p] = forward[q][p]]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                         voteSent, voteVal, decision, alive, faulty, forward>>

ParticipantForward ==
    /\ \E p \in alive :
          /\ pre[p] # notsent
          /\ \E q \in participants :
                /\ q # p
                /\ forward[p][q] = notsent
                /\ forward' = [forward EXCEPT ![p][q] = pre[p]]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                         voteSent, voteVal, decision, alive, faulty, pre>>

ParticipantDecide ==
    /\ \E p \in alive :
          /\ pre[p] # notsent
          /\ \A q \in participants :
                (q = p) \/ forward[p][q] # notsent
          /\ decision' = [decision EXCEPT ![p] = pre[p]]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                         voteSent, voteVal, alive, faulty, pre, forward>>

AbortOnTimeout ==
    /\ \E p \in alive :
          /\ decision[p] = undecided
          /\ coordAlive = FALSE
          /\ \A q \in alive : coordBroadcast[q] = FALSE
          /\ \A q \in participants :
                (q \notin alive) => (\A r \in alive : forward[q][r] = notsent)
          /\ decision' = [decision EXCEPT ![p] = abort]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                         voteSent, voteVal, alive, faulty, pre, forward>>

ParticipantDie ==
    /\ \E p \in alive :
          /\ alive' = alive \ {p}
          /\ faulty' = faulty \cup {p}
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                         voteSent, voteVal, decision, pre, forward>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ ParticipantSendVote
    \/ PreDecideFromCoord
    \/ PreDecideFromForward
    \/ ParticipantForward
    \/ ParticipantDecide
    \/ AbortOnTimeout
    \/ ParticipantDie

\* ----------------------------------------------------------------------
\* Specification
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordBroadcast \in [participants -> BOOLEAN]
    /\ voteSent \subseteq participants
    /\ voteVal \in [participants -> {yes,no}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ alive \subseteq participants
    /\ faulty = participants \\ alive
    /\ pre \in [participants -> {notsent, commit, abort}]
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Required identifiers for the .cfg file
INVARIANTS == TypeInvNB

====