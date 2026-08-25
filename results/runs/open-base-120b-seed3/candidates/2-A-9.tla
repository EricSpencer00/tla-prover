---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    participants,            \* Set of participant identifiers
    yes, no,                \* Vote values
    undecided, commit, abort, \* Decision values
    waiting,               \* (unused placeholder for compatibility)
    notsent                \* Forwarding status meaning no decision sent

VARIABLES 
    coordAlive,            \* TRUE iff coordinator is alive
    coordFaulty,           \* TRUE iff coordinator is faulty (crashed)
    coordDecision,         \* {undecided, commit, abort}
    coordBroadcast,        \* Subset of participants that have already received the coordinator's decision
    participantAlive,      \* [participants -> BOOLEAN]
    participantFaulty,     \* [participants -> BOOLEAN]
    participantDecision,   \* [participants -> {undecided, commit, abort}]
    voteSent,              \* [participants -> BOOLEAN]  (has the participant sent its vote?)
    votes,                 \* [participants -> {yes,no}]
    forwarding             \* [participants -> [participants -> {notsent, commit, abort}]]

\*=====================================================================
\* Type invariant
\*=====================================================================
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordBroadcast \subseteq participants
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ votes \in [participants -> {yes, no}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\*=====================================================================
\* Initial state
\*=====================================================================
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcast = {}
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ votes = [p \in participants |-> yes]          \* arbitrary default
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\*=====================================================================
\* Coordinator actions
\*=====================================================================
CoordMakeDecision ==
    /\ coordDecision = undecided
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcast,
                  participantAlive, participantFaulty,
                  participantDecision, voteSent, votes, forwarding>>

CoordBroadcast ==
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants :
          /\ p \notin coordBroadcast
          /\ coordBroadcast' = coordBroadcast \cup {p}
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                        participantAlive, participantFaulty,
                        participantDecision, voteSent, votes, forwarding>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcast,
                  participantAlive, participantFaulty,
                  participantDecision, voteSent, votes, forwarding>>

\*=====================================================================
\* Participant actions
\*=====================================================================
SendVote(p) ==
    /\ p \in participants
    /\ participantAlive[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ \E v \in {yes, no} : votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantAlive, participantFaulty,
                  participantDecision, forwarding>>

PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ participantAlive[p] = TRUE
    /\ forwarding[p][p] = notsent
    /\ p \in coordBroadcast
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantAlive, participantFaulty,
                  participantDecision, voteSent, votes>>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ participantAlive[p] = TRUE
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ forwarding[q][p] # notsent
          /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantAlive, participantFaulty,
                  participantDecision, voteSent, votes>>

Forward(p, r) ==
    /\ p \in participants /\ r \in participants
    /\ participantAlive[p] = TRUE
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][r] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][r] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantAlive, participantFaulty,
                  participantDecision, voteSent, votes>>

Decide(p) ==
    /\ p \in participants
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ \A r \in participants : forwarding[p][r] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantAlive, participantFaulty,
                  voteSent, votes, forwarding>>

AbortTimeout(p) ==
    /\ p \in participants
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants :
          (participantAlive[q] => q \notin coordBroadcast)
    /\ \A d \in participants :
          (participantAlive[d] = FALSE =>
               \A r \in participants : forwarding[d][r] = notsent)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantAlive, participantFaulty,
                  voteSent, votes, forwarding>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ participantAlive[p] = TRUE
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantDecision, voteSent, votes, forwarding>>

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next ==
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants : \E r \in participants : Forward(p, r)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\*=====================================================================
\* Specification
\*=====================================================================
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                     participantAlive, participantFaulty,
                     participantDecision, voteSent, votes, forwarding>>

\*=====================================================================
\* Invariant collection
\*=====================================================================
INVARIANTS == TypeInvNB

====