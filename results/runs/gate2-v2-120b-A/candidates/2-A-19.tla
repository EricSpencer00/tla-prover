---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    participants, \* Set of participant identifiers
    yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
ParticipantSet == participants
DecisionSet    == {commit, abort, undecided}
VoteSet        == {yes, no}
ForwardStatus  == {notsent, commit, abort}
ParticipantState == {"Alive", "Dead"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,           \* TRUE if coordinator is alive
    coordFaulty,          \* TRUE if coordinator has crashed (faulty)
    coordDecision,        \* decision of coordinator: commit/abort/undecided
    votes,                \* [p \in participants -> VoteSet \cup {undecided}]
    fwdTable,             \* [p \in participants -> [q \in participants -> ForwardStatus]]
    participantState,     \* [p \in participants -> ParticipantState]
    decided,              \* [p \in participants -> DecisionSet]
    voted,                \* [p \in participants -> BOOLEAN]   \* has sent vote
    forwarded,            \* [p \in participants -> [q \in participants -> BOOLEAN]] \* p has forwarded to q
    preDecided            \* [p \in participants -> BOOLEAN]   \* p has stored a pre‑decision

\* ----------------------------------------------------------------------
\* Equality operator for convenience
\* ----------------------------------------------------------------------
\* (no extra definitions needed)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ votes = [p \in participants |-> undecided]
    /\ participantState = [p \in participants |-> "Alive"]
    /\ decided = [p \in participants |-> undecided]
    /\ voted = [p \in participants |-> FALSE]
    /\ fwdTable = [p \in participants |-> [q \in participants |-> notsent]]
    /\ forwarded = [p \in participants |-> [q \in participants |-> FALSE]]
    /\ preDecided = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
AllAlive == {p \in participants : participantState[p] = "Alive"}
AllDecided == {p \in participants : decided[p] # undecided}
NoAliveHasForwarded == 
    \A p \in participants :
        \A q \in participants :
            IF participantState[p] = "Alive" THEN ~forwarded[p][q] ELSE TRUE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Coordinator actions (simplified version of ACP‑SB)
SendRequest ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    participantState, decided, fwdTable,
                    forwarded, preDecided, voted>>

RecvVote(p) ==
    /\ p \in participants
    /\ participantState[p] = "Alive"
    /\ votes[p] = undecided
    /\ voted[p] = FALSE
    /\ \E v \in VoteSet : 
          /\ votes' = [votes EXCEPT ![p] = v]
          /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantState, decided, fwdTable,
                    forwarded, preDecided>>

MakeDecision ==
    /\ coordAlive
    /\ \A p \in participants : votes[p] # undecided
    /\ coordDecision = undecided
    /\ IF \A p \in participants : votes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, votes,
                    participantState, decided, fwdTable,
                    forwarded, preDecided, voted>>

Broadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants :
          /\ participantState[p] = "Alive"
          /\ fwdTable' = [fwdTable EXCEPT ![p][p] = 
                (IF coordDecision = commit THEN commit ELSE abort)]
          /\ preDecided' = [preDecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    participantState, decided, forwarded, voted>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, votes, participantState,
                    decided, fwdTable, forwarded, voted, preDecided>>

\* Participant actions
SendVote(p) ==
    /\ p \in participants
    /\ participantState[p] = "Alive"
    /\ voted[p] = FALSE
    /\ \E v \in VoteSet : 
          /\ votes' = [votes EXCEPT ![p] = v]
          /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantState, decided, fwdTable,
                    forwarded, preDecided>>

PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ participantState[p] = "Alive"
    /\ ~preDecided[p]
    /\ fwdTable[p][p] # notsent
    /\ preDecided' = [preDecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    participantState, decided, fwdTable,
                    forwarded, voted>>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ participantState[p] = "Alive"
    /\ ~preDecided[p]
    /\ \E q \in participants :
          /\ q # p
          /\ fwdTable[q][p] # notsent
    /\ preDecided' = [preDecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    participantState, decided, fwdTable,
                    forwarded, voted>>

Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ participantState[p] = "Alive"
    /\ participantState[q] = "Alive"
    /\ preDecided[p]
    /\ ~forwarded[p][q]
    /\ fwdTable' = [fwdTable EXCEPT ![p][q] = 
            (IF coordDecision = commit THEN commit ELSE abort)]
    /\ forwarded' = [forwarded EXCEPT ![p][q] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    participantState, decided, preDecided, voted>>

Decide(p) ==
    /\ p \in participants
    /\ participantState[p] = "Alive"
    /\ preDecided[p]
    /\ \A q \in participants : 
          q # p => forwarded[p][q]
    /\ decided' = [decided EXCEPT ![p] = 
            (IF fwdTable[p][p] = commit THEN commit ELSE abort)]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    participantState, fwdTable, forwarded,
                    preDecided, voted>>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ participantState[p] = "Alive"
    /\ decided[p] = undecided
    /\ ~coordAlive
    /\ NoAliveHasForwarded
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    participantState, fwdTable, forwarded,
                    preDecided, voted>>

Die(p) ==
    /\ p \in participants
    /\ participantState[p] = "Alive"
    /\ participantState' = [participantState EXCEPT ![p] = "Dead"]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    decided, fwdTable, forwarded, preDecided, voted>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ SendRequest
    \/ \E p \in participants : RecvVote(p)
    \/ MakeDecision
    \/ Broadcast
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision, votes,
                         participantState, decided, fwdTable,
                         forwarded, preDecided, voted>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in DecisionSet
    /\ votes \in [participants -> (VoteSet \cup {undecided})]
    /\ participantState \in [participants -> ParticipantState]
    /\ decided \in [participants -> DecisionSet]
    /\ fwdTable \in [participants -> [participants -> ForwardStatus]]
    /\ forwarded \in [participants -> [participants -> BOOLEAN]]
    /\ preDecided \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]

Agreement ==
    \A p, q \in participants :
        decided[p] = commit => decided[q] = commit

CommitValidity ==
    \A p \in participants :
        decided[p] = commit => \A q \in participants : votes[q] = yes

AbortValidity ==
    \A p \in participants :
        decided[p] = abort =>
            \/ \E q \in participants : votes[q] = no
            \/ coordFaulty
            \/ \E q \in participants : participantState[q] = "Dead"

Irrevocability ==
    \A p \in participants :
        (decided[p] = commit \/ decided[p] = abort) =>
            decided[p]' = decided[p]

\* ----------------------------------------------------------------------
\* The list of invariants requested by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvNB

=============================================================================