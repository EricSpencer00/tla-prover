---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS
    participants, \* set of participant identifiers
    yes, no, undecided, \* vote values
    commit, abort, \* decision values
    waiting,               \* placeholder (not used directly)
    notsent                \* forwarding status meaning “no decision yet”

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    vote,          \* [p \in participants |-> yes | no | undecided]
    alive,         \* subset of participants that are currently up
    decision,      \* [p \in participants |-> commit | abort | undecided]
    faulty,        \* subset of participants that have crashed
    voteSent,      \* [p \in participants |-> BOOLEAN]  (has p sent its vote?)
    coordAlive,    \* BOOLEAN – is the coordinator up?
    coordDecision, \* commit | abort | undecided – decision made by the coordinator
    broadcast,     \* subset of participants that have already received the
                    \* coordinator's broadcast of its decision
    fwd            \* forwarding table:
                    \*   fwd[p][q] = notsent | commit | abort

\* ----------------------------------------------------------------------
\* Helper definitions
AllVotesYes == \A p \in participants: vote[p] = yes
AnyVoteNo   == \E p \in participants: vote[p] = no

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = participants
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = {}
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ broadcast = {}
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP‑SB)
CoordinatorMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ (AllVotesYes \/ AnyVoteNo)
    /\ coordDecision' = IF AllVotesYes THEN commit ELSE abort
    /\ UNCHANGED << vote, alive, decision, faulty, voteSent, broadcast, fwd >>

CoordinatorBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants: p \notin broadcast
    /\ let p == CHOOSE q \in participants: q \notin broadcast IN
       broadcast' = broadcast \cup {p}
    /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordDecision, fwd >>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                    coordDecision, broadcast, fwd >>

\* ----------------------------------------------------------------------
\* Participant actions (base actions)
ParticipantSendVote(p) ==
    /\ p \in alive
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, faulty, coordAlive,
                    coordDecision, broadcast, fwd >>

ParticipantVote(p, v) ==
    /\ p \in alive
    /\ vote[p] = undecided
    /\ v \in {yes, no}
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED << voteSent, decision, faulty, coordAlive,
                    coordDecision, broadcast, fwd >>

ParticipantDie(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED << vote, decision, voteSent, coordAlive,
                    coordDecision, broadcast, fwd >>

\* ----------------------------------------------------------------------
\* New / modified participant actions for reliable broadcast

\* (1) Pre‑decide from coordinator broadcast
ParticipantPreDecideFromCoord(p) ==
    /\ p \in alive
    /\ fwd[p][p] = notsent
    /\ p \in broadcast
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                    coordAlive, coordDecision, broadcast >>

\* (2) Pre‑decide from forwarding by another participant
ParticipantPreDecideFromFwd(p, q) ==
    /\ p \in alive
    /\ fwd[p][p] = notsent
    /\ fwd[q][p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                    coordAlive, coordDecision, broadcast >>

\* (3) Forward the pre‑decision to another participant
ParticipantForward(p, q) ==
    /\ p \in alive
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                    coordAlive, coordDecision, broadcast >>

\* (4) Decide once the pre‑decision has been forwarded to everyone
ParticipantDecide(p) ==
    /\ p \in alive
    /\ fwd[p][p] # notsent
    /\ \A q \in participants: q # p => fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << vote, alive, faulty, voteSent,
                    coordAlive, coordDecision, broadcast, fwd >>

\* (5) Abort on timeout when the coordinator is dead and no decision can be learned
ParticipantAbortTimeout(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants:
          (q \in alive) => q \notin broadcast
    /\ \A q \in participants:
          (q \notin alive) => \A r \in participants:
                               (r \in alive) => fwd[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, voteSent,
                    coordAlive, coordDecision, broadcast, fwd >>

\* ----------------------------------------------------------------------
\* Combined next‑state relation
Next ==
    \E p \in participants:
        \/ ParticipantSendVote(p)
        \/ \E v \in {yes, no}: ParticipantVote(p, v)
        \/ ParticipantPreDecideFromCoord(p)
        \/ \E q \in participants: ParticipantPreDecideFromFwd(p, q)
        \/ \E q \in participants: ParticipantForward(p, q)
        \/ ParticipantDecide(p)
        \/ ParticipantAbortTimeout(p)
        \/ ParticipantDie(p)
    \/ CoordinatorMakeDecision
    \/ CoordinatorBroadcast
    \/ CoordinatorDie

\* ----------------------------------------------------------------------
\* Specification
SpecNB == Init /\ [][Next]_<<vote, alive, decision, faulty, voteSent,
                         coordAlive, coordDecision, broadcast, fwd>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \subseteq participants
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \subseteq participants
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ broadcast \subseteq participants
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* (Optionally) Liveness properties could be added here if desired
\* ----------------------------------------------------------------------
====