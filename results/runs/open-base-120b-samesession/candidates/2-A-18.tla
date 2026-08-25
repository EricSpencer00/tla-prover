---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE if the coordinator is alive
    coordFaulty,         \* TRUE if the coordinator has crashed (faulty)
    coordDecision,       \* decision made by the coordinator (waiting, commit, abort)
    coordSent,           \* mapping participants -> BOOLEAN, true when the coordinator
                         \* has broadcast its decision to that participant
    votes,               \* mapping participants -> {yes,no}
    participantAlive,    \* mapping participants -> BOOLEAN
    participantFaulty,   \* mapping participants -> BOOLEAN
    participantDecision, \* mapping participants -> {undecided, commit, abort}
    fwd                  \* forwarding table:
                         \* fwd[p][q] ∈ {notsent, commit, abort}
                         
vars == << coordAlive, coordFaulty, coordDecision, coordSent,
          votes, participantAlive, participantFaulty,
          participantDecision, fwd >>

\* ----------------------------------------------------------------------
\* Type definitions (used in the type invariant)
\* ----------------------------------------------------------------------
DecisionValues == {commit, abort}
VoteValues     == {yes, no}
ParticipantState == {undecided} \cup DecisionValues

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ coordSent = [p \in participants |-> FALSE]
    /\ votes = [p \in participants |-> yes]            \* arbitrary initial vote
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
\* (1) Decide and broadcast (the simple broadcast step)
CoordDecide ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ (* nondeterministically choose a decision; in a real protocol this depends on votes *)
       coordDecision' \in DecisionValues
    /\ coordSent' = [p \in participants |-> TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, votes,
                    participantAlive, participantFaulty,
                    participantDecision, fwd >>

\* (2) Coordinator crash
CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordSent, votes,
                    participantAlive, participantFaulty,
                    participantDecision, fwd >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* (1) Pre‑decide from coordinator broadcast
PreDecideFromCoord(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ fwd[p][p] = notsent
    /\ coordSent[p] = TRUE
    /\ fwd' = [fwd EXCEPT ![p][p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    votes, participantAlive, participantFaulty,
                    participantDecision, fwd >>

\* (2) Pre‑decide from another participant's forwarding
PreDecideFromFwd(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ fwd[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ fwd[q][p] # notsent
    /\ LET d == IF \E q \in participants : q # p /\ fwd[q][p] = commit
                THEN commit
                ELSE abort
       IN fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    votes, participantAlive, participantFaulty,
                    participantDecision, fwd >>

\* (3) Forward pre‑decision to another participant
Forward(p, q) ==
    /\ participantAlive[p] = TRUE
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    votes, participantAlive, participantFaulty,
                    participantDecision, fwd >>

\* (4) Decide after having forwarded to everybody
Decide(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] =
          IF fwd[p][p] = commit THEN commit ELSE abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    votes, participantAlive, participantFaulty,
                    fwd >>

\* (5) Abort on timeout (coordinator dead and no decision reachable)
AbortTimeout(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : coordSent[q] = FALSE
    /\ \A q \in participants :
          participantAlive[q] = FALSE => 
            \A r \in participants : fwd[q][r] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    votes, participantAlive, participantFaulty,
                    fwd >>

\* (6) Participant crash
ParticipantDie(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    votes, participantDecision, fwd >>

\* ----------------------------------------------------------------------
\* Disjunction of all possible next‑state actions
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p,q \in participants : (p # q) /\ Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordDecide
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant (required by the .cfg file)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {waiting} \cup DecisionValues
    /\ coordSent \in [participants -> BOOLEAN]
    /\ votes \in [participants -> VoteValues]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> ParticipantState]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

====