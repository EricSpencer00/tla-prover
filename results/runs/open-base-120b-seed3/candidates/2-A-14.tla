---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* TRUE iff the coordinator is up
    coordFaulty,         \* TRUE iff the coordinator has crashed
    coordDecision,       \* decision made by the coordinator (commit, abort, or undecided)
    broadcasted,         \* set of participants that have already received the coordinator's broadcast
    votes,               \* participants' votes (yes/no/undecided)
    decisions,           \* final decisions of participants (commit/abort/undecided)
    forwarding,          \* forwarding table: forwarding[p][q] ∈ {commit, abort, notsent}
    alive,               \* set of participants that are currently up
    faulty               \* set of participants that have crashed

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ broadcasted = {}
    /\ votes = [p \in participants |-> undecided]
    /\ decisions = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ alive = participants
    /\ faulty = {}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllForwarded(p) ==
    \A q \in participants : forwarding[p][q] # notsent

ReceivedFromCoordinator(p) ==
    p \in broadcasted

ReceivedFromParticipant(p) ==
    \E r \in participants :
        r # p /\ forwarding[r][p] # notsent

PreDecision(p) ==
    forwarding[p][p] \in {commit, abort}

Decided(p) ==
    decisions[p] # undecided

\* ----------------------------------------------------------------------
\* Coordinator actions (abstracted)
\* ----------------------------------------------------------------------
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED <<coordAlive, coordFaulty, broadcasted, votes, decisions,
                   forwarding, alive, faulty>>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ \E q \in participants :
          q \notin broadcasted
    /\ broadcasted' = broadcasted \cup {q}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                   decisions, forwarding, alive, faulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, broadcasted, votes, decisions,
                   forwarding, alive, faulty>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ p \in participants
    /\ p \in alive
    /\ votes[p] = undecided
    /\ votes' = [votes EXCEPT ![p] = IF RandomChoice({yes,no}) = TRUE THEN yes ELSE no]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted,
                   decisions, forwarding, alive, faulty>>

ParticipantPreDecideFromCoord(p) ==
    /\ p \in participants
    /\ p \in alive
    /\ forwarding[p][p] = notsent
    /\ ReceivedFromCoordinator(p)
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted,
                   votes, decisions, alive, faulty>>

ParticipantPreDecideFromFwd(p) ==
    /\ p \in participants
    /\ p \in alive
    /\ forwarding[p][p] = notsent
    /\ ReceivedFromParticipant(p)
    /\ \E r \in participants :
          r # p /\ forwarding[r][p] # notsent
    /\ LET d == IF forwarding[CHOOSE r \in participants :
                               r # p /\ forwarding[r][p] # notsent][p] = commit
               THEN commit ELSE abort
       IN forwarding' = [forwarding EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted,
                   votes, decisions, alive, faulty>>

ParticipantForward(p,q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ p \in alive
    /\ PreDecision(p)
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted,
                   votes, decisions, alive, faulty>>

ParticipantDecide(p) ==
    /\ p \in participants
    /\ p \in alive
    /\ PreDecision(p)
    /\ AllForwarded(p)
    /\ decisions' = [decisions EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted,
                   votes, forwarding, alive, faulty>>

ParticipantAbortTimeout(p) ==
    /\ p \in participants
    /\ p \in alive
    /\ decisions[p] = undecided
    /\ coordAlive = FALSE
    /\ (broadcasted \cap alive) = {}
    /\ \A r \in participants \ {alive} :
          \A q \in alive : forwarding[r][q] = notsent
    /\ decisions' = [decisions EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted,
                   votes, forwarding, alive, faulty>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted,
                   votes, decisions, forwarding>>

\* ----------------------------------------------------------------------
\* The Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ \E p \in participants : ParticipantPreDecideFromCoord(p)
    \/ \E p \in participants : ParticipantPreDecideFromFwd(p)
    \/ \E p,q \in participants : ParticipantForward(p,q)
    \/ \E p \in participants : ParticipantDecide(p)
    \/ \E p \in participants : ParticipantAbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                      broadcasted, votes, decisions,
                      forwarding, alive, faulty>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ broadcasted \subseteq participants
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ decisions \in [participants -> {commit, abort, undecided}]
    /\ forwarding \in [participants -> [participants -> {commit, abort, notsent}]]
    /\ alive \subseteq participants
    /\ faulty \subseteq participants

====