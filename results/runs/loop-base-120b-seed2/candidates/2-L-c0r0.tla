---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants, \* set of participant identifiers
    yes, no,          \* vote values
    undecided, commit, abort, \* decision values
    waiting,         \* auxiliary value (unused but required)
    notsent          \* forwarding status

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,        \* TRUE iff the coordinator is up
    coordFaulty,       \* TRUE iff the coordinator has crashed
    coordDecision,     \* decision made by the coordinator (undecided/commit/abort)
    votes,             \* [p \in participants |-> yes/no] – the vote each participant will send
    alive,             \* set of participants that are still up
    faulty,            \* set of participants that have crashed
    decision,          \* [p \in participants |-> undecided/commit/abort] – final decision of each participant
    voteSent,          \* set of participants that have already sent their vote
    forwarding         \* [p \in participants |-> [q \in participants |-> notsent/commit/abort]]
    
vars == << coordAlive, coordFaulty, coordDecision,
          votes, alive, faulty, decision, voteSent, forwarding >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ votes = [p \in participants |-> no]          \* initially no vote is assumed
    /\ alive = participants
    /\ faulty = {}
    /\ decision = [p \in participants |-> undecided]
    /\ voteSent = {}
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP‑SB)
\* ----------------------------------------------------------------------
CoordinatorDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, votes, alive, faulty, decision,
                    voteSent, forwarding >>

CoordinatorMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED << votes, alive, faulty, decision, voteSent, forwarding >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* (1) Pre‑decide from coordinator
PreDecideFromCoord ==
    \E p \in participants :
        /\ p \in alive
        /\ decision[p] = undecided
        /\ coordAlive = TRUE
        /\ coordDecision # undecided
        /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                        votes, alive, faulty, decision, voteSent >>

\* (2) Pre‑decide from forwarding by another participant
PreDecideFromForward ==
    \E p, q \in participants :
        /\ p # q
        /\ p \in alive
        /\ decision[p] = undecided
        /\ forwarding[q][p] # notsent
        /\ forwarding[p][p] = undecided
        /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                        votes, alive, faulty, decision, voteSent >>

\* (3) Forward a pre‑decision to another participant
Forward ==
    \E p, q \in participants :
        /\ p # q
        /\ p \in alive
        /\ forwarding[p][p] # undecided
        /\ forwarding[p][q] = notsent
        /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                        votes, alive, faulty, decision, voteSent >>

\* (4) Decide (non‑blocking) after having forwarded to everyone
Decide ==
    \E p \in participants :
        /\ p \in alive
        /\ forwarding[p][p] # undecided
        /\ \A q \in participants : forwarding[p][q] # notsent
        /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                        votes, alive, faulty, voteSent, forwarding >>

\* (5) Abort on timeout
AbortTimeout ==
    \E p \in participants :
        /\ p \in alive
        /\ decision[p] = undecided
        /\ coordAlive = FALSE
        /\ \A q \in participants :
              ~(q \in alive /\ coordDecision # undecided)   \* no alive participant has seen a broadcast
        /\ \A q \in participants :
              ~(q \in faulty /\ \E r \in participants : forwarding[r][p] # notsent) \* no dead participant has forwarded a decision
        /\ decision' = [decision EXCEPT ![p] = abort]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                        votes, alive, faulty, voteSent, forwarding >>

\* (6) Participant crash
ParticipantDie ==
    \E p \in participants :
        /\ p \in alive
        /\ alive' = alive \ {p}
        /\ faulty' = faulty \cup {p}
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                        votes, decision, voteSent, forwarding >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordinatorDie
    \/ CoordinatorMakeDecision
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
    /\ coordDecision \in {undecided, commit, abort}
    /\ votes \in [participants -> {yes, no}]
    /\ alive \subseteq participants
    /\ faulty \subseteq participants
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ voteSent \subseteq participants
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Liveness properties (stated for completeness – not required by the cfg)
\* ----------------------------------------------------------------------
\* AC5: every non‑faulty participant eventually decides
AC5 == \A p \in participants :
          <> (p \in faulty \/ decision[p] # undecided)

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesTypeInv == SpecNB => []TypeInvNB

====