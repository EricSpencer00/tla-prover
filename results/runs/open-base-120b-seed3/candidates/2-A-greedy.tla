---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* BOOLEAN  (TRUE = coordinator up)
    coordFaulty,         \* BOOLEAN  (TRUE = coordinator crashed)
    coordDecision,      \* {commit, abort, undecided}
    coordVotes,         \* SUBSET participants   (set of participants from which a vote has been received)
    coordBroadcasted,   \* SUBSET participants   (set of participants to which the coordinator has sent its decision)
    vote,               \* [participants -> {yes,no}]
    alive,              \* [participants -> BOOLEAN]   (TRUE = participant up)
    faulty,             \* [participants -> BOOLEAN]   (TRUE = participant crashed)
    decision,           \* [participants -> {undecided, commit, abort}]
    voteSent,           \* [participants -> BOOLEAN]   (TRUE = vote already sent)
    forwarding          \* [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision, coordVotes,
           coordBroadcasted, vote, alive, faulty, decision,
           voteSent, forwarding >>

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordVotes \subseteq participants
    /\ coordBroadcasted \subseteq participants
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordVotes = {}
    /\ coordBroadcasted = {}
    /\ vote = [p \in participants |-> yes]   \* initial vote value is nondeterministic; will be overwritten by SendVote
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordinatorReceiveVote(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ alive[p]
    /\ ~voteSent[p]               \* participant has not yet sent its vote
    /\ vote[p] \in {yes, no}
    /\ coordVotes' = coordVotes \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, vote, alive, faulty,
                    decision, voteSent, forwarding >>

CoordinatorMakeDecision ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordVotes = participants
    /\ IF \A p \in participants: vote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordVotes,
                    coordBroadcasted, vote, alive, faulty,
                    decision, voteSent, forwarding >>

CoordinatorBroadcast ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants: p \notin coordBroadcasted
    /\ LET p == CHOOSE q \in participants : q \notin coordBroadcasted IN
          coordBroadcasted' = coordBroadcasted \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, vote, alive, faulty,
                    decision, voteSent, forwarding >>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordVotes, coordBroadcasted,
                    vote, alive, faulty, decision, voteSent, forwarding >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ vote' = [vote EXCEPT ![p] = (IF RandomElement({yes, no}) = yes THEN yes ELSE no)]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    alive, faulty, decision, forwarding >>

ParticipantPreDecideFromCoordinator(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decision[p] = undecided
    /\ forwarding[p][p] = notsent
    /\ p \in coordBroadcasted
    /\ forwarding' = [forwarding EXCEPT ![p][p] = (IF coordDecision = commit THEN commit ELSE abort)]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    vote, alive, faulty, decision, voteSent >>

ParticipantPreDecideFromForward(p, q) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decision[p] = undecided
    /\ forwarding[p][p] = notsent
    /\ forwarding[q][p] \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    vote, alive, faulty, decision, voteSent >>

ParticipantForward(p, q) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    vote, alive, faulty, decision, voteSent >>

ParticipantDecide(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ forwarding[p][p] \in {commit, abort}
    /\ \A q \in participants: forwarding[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = (IF forwarding[p][p] = commit THEN commit ELSE abort)]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    vote, alive, faulty, voteSent, forwarding >>

ParticipantAbortTimeout(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants: q \notin coordBroadcasted
    /\ \A d \in participants:
          ( ~alive[d] => \A a \in participants:
                (alive[a] => forwarding[d][a] = notsent) )
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    vote, alive, faulty, voteSent, forwarding >>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    vote, decision, voteSent, forwarding >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: CoordinatorReceiveVote(p)
    \/ CoordinatorMakeDecision
    \/ CoordinatorBroadcast
    \/ CoordinatorDie
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantPreDecideFromCoordinator(p)
    \/ \E p,q \in participants: ParticipantPreDecideFromForward(p,q)
    \/ \E p,q \in participants: ParticipantForward(p,q)
    \/ \E p \in participants: ParticipantDecide(p)
    \/ \E p \in participants: ParticipantAbortTimeout(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant (type correctness)
\* ----------------------------------------------------------------------
THEOREM TypeInvNBIsInvariant == SpecNB => []TypeInvNB

====