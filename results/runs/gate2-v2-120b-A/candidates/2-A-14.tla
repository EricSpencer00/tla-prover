---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    participants,          \* Set of participant identifiers
    yes, no,               \* Vote values
    undecided, commit, abort, waiting, notsent

\* ==============================================================================
\* Types
\* ==============================================================================
Vote == {yes, no}
DecisionValue == {commit, abort}
ForwardStatus == {notsent, commit, abort}
PreDecision == DecisionValue \cup {notsent}
ParticipantState == {waiting, undecided, commit, abort}
CoordState == {"idle", "waiting", "decided"}

\* ==============================================================================
\* Variables
\* ==============================================================================
VARIABLES
    alive,          \* Set of alive actors (participants ∪ {"coord"})
    faulty,         \* Set of faulty (crashed) actors
    coordState,     \* Coordinator's internal state
    coordDecision,  \* Coordinator's decision (if any)
    votes,          \* [p \in participants -> Vote]  votes sent by participants
    voted,          \* Set of participants that have already sent their vote
    participantState, \* [p \in participants -> ParticipantState]
    preDecisions,   \* [p \in participants -> PreDecision]   (own entry)
    forwardTable    \* [p \in participants -> [q \in participants -> ForwardStatus]]

\* ==============================================================================
\* Initial state
\* ==============================================================================
Init ==
    /\ alive = participants \cup {"coord"}
    /\ faulty = {}
    /\ coordState = "idle"
    /\ coordDecision = "none"
    /\ votes = [p \in participants |-> "none"]
    /\ voted = {}
    /\ participantState = [p \in participants |-> waiting]
    /\ preDecisions = [p \in participants |-> notsent]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ==============================================================================
\* Helper definitions
\* ==============================================================================
IsFaulty(a) == a \in faulty
IsAlive(a) == a \in alive

AliveParticipants == participants \cap alive
FaultyParticipants == participants \cap faulty

\* ==============================================================================
\* Coordinator actions (inherited from ACP‑SB)
\* ==============================================================================
CoordSendRequest ==
    /\ coordState = "idle"
    /\ coordState' = "waiting"
    /\ UNCHANGED <<coordDecision, votes, voted, participantState,
                   preDecisions, forwardTable, alive, faulty>>

CoordReceiveVote(p) ==
    /\ p \in participants
    /\ IsAlive(p)
    /\ coordState = "waiting"
    /\ votes[p] = "none"
    /\ votes' = [votes EXCEPT ![p] = votes[p]]
    /\ voted' = voted \cup {p}
    /\ UNCHANGED <<coordDecision, participantState,
                   preDecisions, forwardTable, alive, faulty, coordState>>

CoordMakeDecision ==
    /\ coordState = "waiting"
    /\ voted = participants
    /\ \A p \in participants: votes[p] = yes
    /\ coordDecision' = commit
    /\ coordState' = "decided"
    /\ UNCHANGED <<votes, voted, participantState,
                   preDecisions, forwardTable, alive, faulty>>

CoordMakeAbort ==
    /\ coordState = "waiting"
    /\ \E p \in participants: votes[p] = no
    /\ coordDecision' = abort
    /\ coordState' = "decided"
    /\ UNCHANGED <<votes, voted, participantState,
                   preDecisions, forwardTable, alive, faulty>>

CoordBroadcast ==
    /\ coordState = "decided"
    /\ \A p \in participants: IsAlive(p) => preDecisions[p] = notsent
    /\ forwardTable' = [forwardTable EXCEPT
          ![p][p] = coordDecision :> (commit |-> commit, abort |-> abort)]
    /\ UNCHANGED <<coordDecision, votes, voted, participantState,
                   preDecisions, alive, faulty, coordState>>

CoordDie ==
    /\ IsAlive("coord")
    /\ faulty' = faulty \cup {"coord"}
    /\ alive' = alive \ {"coord"}
    /\ UNCHANGED <<coordState, coordDecision, votes, voted,
                   participantState, preDecisions, forwardTable>>

\* ==============================================================================
\* Participant actions
\* ==============================================================================
ParticipantSendVote(p) ==
    /\ p \in participants
    /\ IsAlive(p)
    /\ participantState[p] = waiting
    /\ votes' = [votes EXCEPT ![p] = yes]    \* (for simplicity participants always vote yes)
    /\ participantState' = [participantState EXCEPT ![p] = undecided]
    /\ UNCHANGED <<coordDecision, coordState, voted, preDecisions,
                   forwardTable, alive, faulty>>

ParticipantPreDecideFromCoord(p) ==
    /\ p \in participants
    /\ IsAlive(p)
    /\ preDecisions[p] = notsent
    /\ coordState = "decided"
    /\ forwardTable[p][p] = notsent
    /\ preDecisions' = [preDecisions EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordDecision, coordState, votes, voted,
                   participantState, forwardTable, alive, faulty>>

ParticipantPreDecideFromForward(p) ==
    /\ p \in participants
    /\ IsAlive(p)
    /\ preDecisions[p] = notsent
    /\ \E q \in participants: q # p /\ forwardTable[q][p] # notsent
    /\ preDecisions' = [preDecisions EXCEPT ![p] = forwardTable[CHOOSE q \in participants:
                                                    q # p /\ forwardTable[q][p] # notsent][p]]
    /\ UNCHANGED <<coordDecision, coordState, votes, voted,
                   participantState, forwardTable, alive, faulty>>

ParticipantForward(p) ==
    /\ p \in participants
    /\ IsAlive(p)
    /\ preDecisions[p] # notsent
    /\ \E q \in participants: q # p /\ forwardTable[p][q] = notsent
    /\ LET q == CHOOSE r \in participants: r # p /\ forwardTable[p][r] = notsent IN
       forwardTable' = [forwardTable EXCEPT ![p][q] = preDecisions[p]]
    /\ UNCHANGED <<coordDecision, coordState, votes, voted,
                   participantState, preDecisions, alive, faulty>>

ParticipantDecide(p) ==
    /\ p \in participants
    /\ IsAlive(p)
    /\ preDecisions[p] # notsent
    /\ \A q \in participants: q # p => forwardTable[p][q] = preDecisions[p]
    /\ participantState[p] = undecided
    /\ participantState' = [participantState EXCEPT ![p] = 
          (IF preDecisions[p] = commit THEN commit ELSE abort)]
    /\ UNCHANGED <<coordDecision, coordState, votes, voted,
                   preDecisions, forwardTable, alive, faulty>>

ParticipantAbortTimeout(p) ==
    /\ p \in participants
    /\ IsAlive(p)
    /\ participantState[p] \notin {commit, abort}
    /\ ~ IsAlive("coord")
    /\ \A q \in participants: forwardTable[q][p] = notsent
    /\ participantState' = [participantState EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordDecision, coordState, votes, voted,
                   preDecisions, forwardTable, alive, faulty>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ IsAlive(p)
    /\ faulty' = faulty \cup {p}
    /\ alive' = alive \ {p}
    /\ UNCHANGED <<coordDecision, coordState, votes, voted,
                   participantState, preDecisions, forwardTable>>

\* ==============================================================================
\* Combined Next action
\* ==============================================================================
Next ==
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantPreDecideFromCoord(p)
    \/ \E p \in participants: ParticipantPreDecideFromForward(p)
    \/ \E p \in participants: ParticipantForward(p)
    \/ \E p \in participants: ParticipantDecide(p)
    \/ \E p \in participants: ParticipantAbortTimeout(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ CoordSendRequest
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ CoordMakeDecision
    \/ CoordMakeAbort
    \/ CoordBroadcast
    \/ CoordDie

\* ==============================================================================
\* Specification
\* ==============================================================================
SpecNB == Init /\ [][Next]_<<coordDecision, coordState, alive, faulty,
                         votes, voted, participantState,
                         preDecisions, forwardTable>>

\* ==============================================================================
\* Invariant (type correctness)
\* ==============================================================================
TypeInvNB ==
    /\ alive = (participants \cup {"coord"}) \ faulty
    /\ coordState \in {"idle", "waiting", "decided"}
    /\ coordDecision \in {"none", commit, abort}
    /\ votes \in [participants -> {"none"} \cup Vote]
    /\ voted \subseteq participants
    /\ participantState \in [participants -> ParticipantState]
    /\ preDecisions \in [participants -> PreDecision]
    /\ forwardTable \in [participants -> [participants -> ForwardStatus]]

=============================================================================