---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    participants,       \* Set of participant identifiers
    yes, no,            \* Vote values
    undecided, commit, abort,   \* Decision values for participants
    waiting,            \* Not used directly but required by the cfg
    notsent             \* Forwarding status meaning no decision forwarded yet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* Boolean: coordinator is alive
    coordFaulty,         \* Boolean: coordinator is faulty (has crashed)
    coordDecision,       \* The decision made by the coordinator (commit, abort or "none")
    broadcasted,         \* Set of participants to which the coordinator has already broadcasted the decision
    vote,                \* Mapping participant -> {yes, no, "none"}
    voteSent,            \* Mapping participant -> Boolean indicating whether the vote has been sent
    alive,               \* Mapping participant -> Boolean (true = alive)
    decision,            \* Mapping participant -> {undecided, commit, abort}
    faulty,              \* Mapping participant -> Boolean (true = faulty)
    forwarding           \* Mapping participant -> (Mapping participant -> {notsent, commit, abort})

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
VoteVals == {yes, no, "none"}
CoordDecVals == {commit, abort, "none"}

TypeInvNB == 
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in CoordDecVals
    /\ broadcasted \subseteq participants
    /\ vote \in [participants -> VoteVals]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ broadcasted = {}
    /\ vote = [p \in participants |-> "none"]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ \A p \in participants: voteSent[p] = TRUE
    /\ ( \A p \in participants: vote[p] = yes
         => coordDecision' = commit )
    /\ ( \E p \in participants: vote[p] = no
         => coordDecision' = abort )
    /\ UNCHANGED <<coordAlive, coordFaulty, broadcasted, vote, voteSent, alive, decision, faulty, forwarding>>

CoordBroadcast ==
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants \ broadcasted : 
         /\ broadcasted' = broadcasted \cup {p}
         /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, vote, voteSent, alive, decision, faulty, forwarding>>
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, vote, voteSent, alive, decision, faulty, forwarding>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, broadcasted, vote, voteSent, alive, decision, faulty, forwarding>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ \/ vote' = [vote EXCEPT ![p] = yes]
       \/ vote' = [vote EXCEPT ![p] = no]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted, alive, decision, faulty, forwarding>>

ParticipantPreDecideFromCoord(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ forwarding[p][p] = notsent
    /\ p \in broadcasted
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted, vote, voteSent, alive, decision, faulty>>

ParticipantPreDecideFromForward(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants : q # p /\ forwarding[q][p] # notsent
    /\ LET d == CHOOSE q \in participants : q # p /\ forwarding[q][p] # notsent
       IN forwarding' = [forwarding EXCEPT ![p][p] = forwarding[d][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted, vote, voteSent, alive, decision, faulty>>

ParticipantForward(p,q) ==
    /\ p \in participants /\ q \in participants
    /\ alive[p] = TRUE
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted, vote, voteSent, alive, decision, faulty, voteSent>>

ParticipantDecide(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ forwarding[p][p] \in {commit, abort}
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted, vote, voteSent, alive, faulty, forwarding>>

ParticipantAbortTimeout(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ broadcasted = {}
    /\ \A r \in participants : faulty[r] => \A s \in participants : forwarding[r][s] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted, vote, voteSent, alive, faulty, forwarding>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcasted, vote, voteSent, decision, forwarding>>

\* ----------------------------------------------------------------------
\* Combined next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ \E p \in participants : ParticipantPreDecideFromCoord(p)
    \/ \E p \in participants : ParticipantPreDecideFromForward(p)
    \/ \E p \in participants : \E q \in participants : ParticipantForward(p,q)
    \/ \E p \in participants : ParticipantDecide(p)
    \/ \E p \in participants : ParticipantAbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision, broadcasted,
                        vote, voteSent, alive, decision, faulty, forwarding>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvNB

====