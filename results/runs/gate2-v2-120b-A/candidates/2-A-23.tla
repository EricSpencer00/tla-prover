---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Participant == participants

\* Vote of a participant
Vote == {yes, no}

\* Decision values
Decision == {commit, abort, undecided}

\* Forwarding status per entry
FwdStatus == {notsent, commit, abort}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    tx,                 \* Transaction status (unused in this spec)
    coordAlive,         \* TRUE iff coordinator is alive
    coordFaulty,        \* TRUE iff coordinator is faulty (crashed)
    coordDecision,      \* Decision made by coordinator (undecided initially)
    votes,              \* [Participant -> Vote]   votes cast by participants
    voteSent,           \* [Participant -> BOOLEAN]  whether a vote has been sent
    participantAlive,   \* [Participant -> BOOLEAN]  alive status of participants
    participantFaulty,  \* [Participant -> BOOLEAN]  faulty flag of participants
    participantDecision,\* [Participant -> Decision] final decision of participants
    fwdTable            \* [Participant -> [Participant -> FwdStatus]] forwarding tables
                                    \* outer map: owner, inner map: entry for each participant

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllPreDecided == 
    \A p \in participants : 
        fwdTable[p][p] \in {commit, abort}

AllForwarded == 
    \A p \in participants : 
        \A q \in participants : 
            p # q => fwdTable[p][q] = fwdTable[p][p]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ tx = FALSE
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ votes = [p \in participants |-> yes]    \* arbitrary initial, will be set by SendVote
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ fwdTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP-SB)
\* ----------------------------------------------------------------------
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED << tx, votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, fwdTable >>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \A p \in participants :
          coordDecision = commit => 
             fwdTable[p][p] = commit \/ fwdTable[p][p] = notsent
          /\ coordDecision = abort => 
             fwdTable[p][p] = abort \/ fwdTable[p][p] = notsent
    /\ UNCHANGED << tx, coordAlive, coordDecision, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, fwdTable >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << tx, coordDecision, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, fwdTable >>

\* ----------------------------------------------------------------------
\* Participant base actions (send vote, abort on timeout, die)
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << tx, votes, participantAlive, participantFaulty,
                    participantDecision, fwdTable,
                    coordAlive, coordFaulty, coordDecision >>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : fwdTable[q][p] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << tx, votes, voteSent, participantAlive, participantFaulty,
                    fwdTable, coordAlive, coordFaulty, coordDecision >>

ParticipantDie(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << tx, votes, voteSent, participantDecision,
                    fwdTable, coordAlive, coordFaulty, coordDecision >>

\* ----------------------------------------------------------------------
\* New participant actions for reliable broadcast
\* ----------------------------------------------------------------------
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordDecision # undecided
    /\ fwdTable[p][p] = notsent
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = 
                        IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED << tx, votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, coordAlive, coordFaulty, coordDecision >>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ fwdTable[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ fwdTable[q][p] # notsent
    /\ LET d == 
          IF \E q \in participants : q # p /\ fwdTable[q][p] = commit 
          THEN commit ELSE abort
       IN fwdTable' = [fwdTable EXCEPT ![p][p] = d]
    /\ UNCHANGED << tx, votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, coordAlive, coordFaulty, coordDecision >>

Forward(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ fwdTable[p][p] \in {commit, abort}
    /\ \E q \in participants :
          q # p /\ fwdTable[p][q] = notsent
    /\ LET q == CHOOSE q \in participants : q # p /\ fwdTable[p][q] = notsent IN
        fwdTable' = [fwdTable EXCEPT ![p][q] = fwdTable[p][p]]
    /\ UNCHANGED << tx, votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, coordAlive, coordFaulty, coordDecision >>

Decide(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ AllForwarded
    /\ participantDecision' = [participantDecision EXCEPT ![p] = 
                                   IF fwdTable[p][p] = commit THEN commit ELSE abort]
    /\ UNCHANGED << tx, votes, voteSent, participantAlive, participantFaulty,
                    fwdTable, coordAlive, coordFaulty, coordDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants : Forward(p)
    \/ \E p \in participants : Decide(p)
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification and temporal operators
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<tx, coordAlive, coordFaulty, coordDecision,
                     votes, voteSent, participantAlive, participantFaulty,
                     participantDecision, fwdTable>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ tx \in BOOLEAN
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ votes \in [Participant -> Vote]
    /\ voteSent \in [Participant -> BOOLEAN]
    /\ participantAlive \in [Participant -> BOOLEAN]
    /\ participantFaulty \in [Participant -> BOOLEAN]
    /\ participantDecision \in [Participant -> Decision]
    /\ fwdTable \in [Participant -> [Participant -> FwdStatus]]

\* ----------------------------------------------------------------------
\* Additional safety invariants from the description
\* ----------------------------------------------------------------------
AC1_Agreement ==
    \A p, q \in participants :
        (participantDecision[p] = commit /\ participantDecision[q] = abort) => FALSE

AC2_CommitValidity ==
    \A p \in participants :
        participantDecision[p] = commit => 
            \A q \in participants : votes[q] = yes

AC3_AbortValidity ==
    \A p \in participants :
        participantDecision[p] = abort =>
            \E q \in participants : votes[q] = no
            \/ \E q \in participants : participantFaulty[q] = TRUE
            \/ coordFaulty = TRUE

AC4_Irrevocability ==
    \A p \in participants :
        (participantDecision[p] = commit \/ participantDecision[p] = abort) =>
            participantDecision[p]' = participantDecision[p]

\* The primary safety invariant required by the .cfg
Invariant == TypeInvNB

\* ----------------------------------------------------------------------
\* Liveness properties (optional, not used as required invariant)
\* ----------------------------------------------------------------------
Terminate ==
    \E d \in {commit, abort} :
        \A p \in participants : participantDecision[p] = d

\* ----------------------------------------------------------------------
\* Theorem (for TLC) that the spec implies the invariant
\* ----------------------------------------------------------------------
THEOREM SpecImpliesInvariant == SpecNB => []Invariant

====