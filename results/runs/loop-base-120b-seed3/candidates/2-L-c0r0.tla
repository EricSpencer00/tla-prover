---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no,        \* vote values
    undecided, commit, abort,   \* decision values for participants
    waiting,       \* coordinator request state (unused but required)
    notsent        \* forwarding table entry meaning “no decision sent”

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* BOOLEAN – coordinator is alive
    coordFaulty,         \* BOOLEAN – coordinator is faulty (crashed)
    coordDecision,       \* {"none", commit, abort} – decision made by coordinator
    votes,               \* [participants -> {yes,no}]
    voteSent,            \* [participants -> BOOLEAN] – has the participant sent its vote?
    participantAlive,    \* SUBSET participants – participants that are still alive
    participantFaulty,   \* SUBSET participants – participants that have crashed
    participantDecision, \* [participants -> {undecided, commit, abort}]
    forwarding           \* [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision,
           votes, voteSent,
           participantAlive, participantFaulty,
           participantDecision, forwarding >>

AllParticipants == participants

\* The set of participants that have already received a pre‑decision
PreDecided(p) == forwarding[p][p] # notsent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ votes = [p \in participants |-> no]          \* arbitrary initial vote
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = participants
    /\ participantFaulty = {}
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP‑SB)
\* ----------------------------------------------------------------------
CoordinatorMakeDecision ==
    /\ coordAlive
    /\ coordDecision = "none"
    /\ \A p \in participants: voteSent[p]               \* all votes have been received
    /\ IF \A p \in participants: votes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding >>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participantAlive
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    participantDecision, forwarding >>

PreDecideFromCoord(p) ==
    /\ p \in participantAlive
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ forwarding[p][p] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision >>

PreDecideFromForward(p) ==
    /\ p \in participantAlive
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
          forwarding[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} :
                \E q \in participants : forwarding[q][p] = d
       IN forwarding' = [forwarding EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision >>

Forward(p, q) ==
    /\ p \in participantAlive
    /\ q \in participants
    /\ p # q
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision >>

Decide(p) ==
    /\ p \in participantAlive
    /\ forwarding[p][p] \in {commit, abort}
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    forwarding >>

AbortTimeout(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ coordFaulty
    /\ \A q \in participants :
          ~ (coordAlive /\ coordDecision \in {commit, abort} /\ forwarding[q][p] # notsent)
    /\ \A q \in participants :
          ~ (q \notin participantAlive /\ \E r \in participants : forwarding[r][p] # notsent)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    forwarding >>

ParticipantDie(p) ==
    /\ p \in participantAlive
    /\ participantAlive' = participantAlive \ {p}
    /\ participantFaulty' = participantFaulty \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantDecision, forwarding >>

\* ----------------------------------------------------------------------
\* The overall next‑state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ CoordinatorMakeDecision
    \/ CoordinatorDie
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Fairness assumptions (weak fairness on progress actions, excluding death)
\* ----------------------------------------------------------------------
ParticipantProgress ==
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : SendVote(p)

CoordinatorProgress ==
    \/ CoordinatorMakeDecision

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB ==
    Init /\ [][Next]_vars /\ WF_vars(ParticipantProgress) /\ WF_vars(CoordinatorProgress)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {"none", commit, abort}
    /\ votes \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ participantAlive \subseteq participants
    /\ participantFaulty \subseteq participants
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

====