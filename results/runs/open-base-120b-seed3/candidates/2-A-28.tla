---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* --------------------------------------------------------------
\* Variables
\* --------------------------------------------------------------
VARIABLES 
    coordAlive,          \* BOOLEAN: coordinator is up
    coordFaulty,         \* BOOLEAN: coordinator is faulty (crashed)
    coordDecision,       \* ONE OF {commit, abort, undecided}
    coordBroadcast,      \* SUBSET participants that have already received the broadcast
    votes,               \* [participants -> {yes,no}]
    voteSent,            \* [participants -> BOOLEAN]
    participantAlive,    \* SUBSET participants
    participantFaulty,   \* SUBSET participants
    participantDecision, \* [participants -> {undecided, commit, abort}]
    forwarding           \* [participants -> [participants -> {notsent, commit, abort}]]

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------
Alive(p) == p \in participantAlive
PreDecided(p) == forwarding[p][p] # notsent
AllForwarded(p) == \A q \in participants \ {p} : forwarding[p][q] # notsent
CoordSent(p) == p \in coordBroadcast

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcast = {}
    /\ votes = [p \in participants |-> yes]            \* initial placeholder
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = participants
    /\ participantFaulty = {}
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* --------------------------------------------------------------
\* Coordinator actions
\* --------------------------------------------------------------
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcast, votes, voteSent,
                   participantAlive, participantFaulty,
                   participantDecision, forwarding>>

MakeDecision ==
    /\ coordAlive
    /\ \A p \in participants : voteSent[p]          \* all votes have been sent
    /\ coordDecision' = IF \A p \in participants : votes[p] = yes
                         THEN commit
                         ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcast,
                   votes, voteSent, participantAlive,
                   participantFaulty, participantDecision,
                   forwarding>>

BroadcastDecision ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants : ~CoordSent(p)        \* there is a participant not yet broadcasted to
    /\ \E p \in participants :
          /\ ~CoordSent(p)
          /\ coordBroadcast' = coordBroadcast \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, voteSent, participantAlive,
                   participantFaulty, participantDecision,
                   forwarding>>

\* --------------------------------------------------------------
\* Participant actions
\* --------------------------------------------------------------

Vote(p, v) ==
    /\ Alive(p)
    /\ ~voteSent[p]
    /\ v \in {yes, no}
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcast, participantAlive,
                   participantFaulty, participantDecision,
                   forwarding>>

PreDecideFromCoord(p) ==
    /\ Alive(p)
    /\ forwarding[p][p] = notsent
    /\ CoordSent(p)
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcast, votes, voteSent,
                   participantAlive, participantFaulty,
                   participantDecision>>

PreDecideFromForward(p) ==
    /\ Alive(p)
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ forwarding[q][p] # notsent
    /\ LET d == IF \E q \in participants :
                     q # p /\ forwarding[q][p] = commit
                 THEN commit
                 ELSE abort
       IN forwarding' = [forwarding EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcast, votes, voteSent,
                   participantAlive, participantFaulty,
                   participantDecision>>

Forward(p, r) ==
    /\ Alive(p)
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][r] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][r] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcast, votes, voteSent,
                   participantAlive, participantFaulty,
                   participantDecision>>

Decide(p) ==
    /\ Alive(p)
    /\ forwarding[p][p] # notsent
    /\ AllForwarded(p)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcast, votes, voteSent,
                   participantAlive, participantFaulty,
                   forwarding>>

AbortTimeout(p) ==
    /\ Alive(p)
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants :
          (q \in participantAlive) => ~CoordSent(q)          \* no alive participant received broadcast
    /\ \A q \in participants :
          (q \notin participantAlive) =>
              \A r \in participants : forwarding[q][r] = notsent   \* no dead participant forwarded a decision
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcast, votes, voteSent,
                   participantAlive, participantFaulty,
                   forwarding>>

PartDie(p) ==
    /\ Alive(p)
    /\ participantAlive' = participantAlive \ {p}
    /\ participantFaulty' = participantFaulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcast, votes, voteSent,
                   participantDecision, forwarding>>

\* --------------------------------------------------------------
\* Next-state relation
\* --------------------------------------------------------------
Next ==
    \/ CoordDie
    \/ MakeDecision
    \/ BroadcastDecision
    \/ \E p \in participants :
          \/ \E v \in {yes, no} : Vote(p, v)
          \/ PreDecideFromCoord(p)
          \/ PreDecideFromForward(p)
          \/ \E r \in participants \ {p} : Forward(p, r)
          \/ Decide(p)
          \/ AbortTimeout(p)
          \/ PartDie(p)

vars == <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
          votes, voteSent,
          participantAlive, participantFaulty,
          participantDecision, forwarding>>

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* --------------------------------------------------------------
\* Type invariant
\* --------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordBroadcast \subseteq participants
    /\ votes \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ participantAlive \subseteq participants
    /\ participantFaulty \subseteq participants
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\* --------------------------------------------------------------
\* End of module
\* --------------------------------------------------------------
====