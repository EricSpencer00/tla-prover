---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    participants, \* set of participant identifiers
    yes, no, undecided, \* vote values
    commit, abort, \* final decision values
    waiting, notsent \* auxiliary constants used in tables

\* Types (for readability)
VoteVals   == {yes, no}
DecVals    == {commit, abort, undecided}
FwdStatus  == {notsent, commit, abort}

\************************************************************************
\* State variables
\************************************************************************
VARIABLES
    coordAlive,      \* Boolean: coordinator up?
    coordFaulty,     \* Boolean: coordinator faulty?
    coordDecision,   \* One of DecVals, value broadcast by coordinator (or undecided)
    votes,           \* [participants -> VoteVals]   votes cast by participants
    voteSent,        \* [participants -> BOOLEAN]    whether participant has sent its vote
    fwdTable,        \* [participants -> [participants -> FwdStatus]] forwarding table
    decisions,       \* [participants -> DecVals]    final decisions (undecided until decided)
    faulty           \* [participants -> BOOLEAN]    participant faulty flag

\************************************************************************
\* Helper definitions
\************************************************************************
ParticipantSet == participants

AliveParts == { p \in ParticipantSet : ~faulty[p] }

AllDecided == \A p \in ParticipantSet : decisions[p] # undecided

\************************************************************************
\* Initial state
\************************************************************************
Init ==
    /\ coordAlive  = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ votes = [p \in ParticipantSet |-> yes]   \* initially all vote yes (can be changed by vote actions)
    /\ voteSent = [p \in ParticipantSet |-> FALSE]
    /\ decisions = [p \in ParticipantSet |-> undecided]
    /\ faulty = [p \in ParticipantSet |-> FALSE]
    /\ fwdTable = [p \in ParticipantSet |-> [q \in ParticipantSet |-> notsent]]

\************************************************************************
\* Coordinator actions (imported from ACP-SB)
\************************************************************************
CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E d \in {commit, abort} :
        /\ coordDecision = d
        /\ \A p \in ParticipantSet :
            /\ fwdTable[p][p] = d

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, votes, voteSent, decisions, faulty, fwdTable >>

\************************************************************************
\* Participant actions
\************************************************************************
SendVote(p) ==
    /\ p \in ParticipantSet
    /\ ~faulty[p]
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, votes,
                    decisions, faulty, fwdTable >>

PreDecFromCoord(p) ==
    /\ p \in ParticipantSet
    /\ ~faulty[p]
    /\ fwdTable[p][p] = notsent
    /\ coordDecision \in {commit, abort}
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, decisions, faulty >>

PreDecFromFwd(p) ==
    /\ p \in ParticipantSet
    /\ ~faulty[p]
    /\ fwdTable[p][p] = notsent
    /\ \E q \in ParticipantSet :
        /\ q # p
        /\ fwdTable[q][p] # notsent
        /\ fwdTable[p][p] = fwdTable[q][p]   \* adopt the decision forwarded
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, decisions, faulty, fwdTable >>

Forward(p, q) ==
    /\ p \in ParticipantSet
    /\ q \in ParticipantSet
    /\ p # q
    /\ ~faulty[p]
    /\ ~faulty[q]
    /\ fwdTable[p][p] # notsent           \* p has a pre‑decision
    /\ fwdTable[p][q] = notsent           \* has not yet forwarded to q
    /\ fwdTable' = [fwdTable EXCEPT ![p][q] = fwdTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, decisions, faulty >>

Decide(p) ==
    /\ p \in ParticipantSet
    /\ ~faulty[p]
    /\ fwdTable[p][p] # notsent
    /\ \A q \in ParticipantSet : q # p => fwdTable[p][q] # notsent
    /\ decisions[p] = fwdTable[p][p]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, faulty, fwdTable >>

AbortOnTimeout(p) ==
    /\ p \in ParticipantSet
    /\ ~faulty[p]
    /\ decisions[p] = undecided
    /\ ~coordAlive
    /\ \A q \in ParticipantSet :
        (coordDecision = undecided) \/ (fwdTable[q][p] = notsent)
    /\ decisions' = [decisions EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, faulty, fwdTable >>

Die(p) ==
    /\ p \in ParticipantSet
    /\ ~faulty[p]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, decisions, fwdTable >>

\************************************************************************
\* Next-state relation
\************************************************************************
Next ==
    \/ \E p \in ParticipantSet : SendVote(p)
    \/ \E p \in ParticipantSet : PreDecFromCoord(p)
    \/ \E p \in ParticipantSet : PreDecFromFwd(p)
    \/ \E p,q \in ParticipantSet : Forward(p,q)
    \/ \E p \in ParticipantSet : Decide(p)
    \/ \E p \in ParticipantSet : AbortOnTimeout(p)
    \/ \E p \in ParticipantSet : Die(p)
    \/ CoordBroadcast
    \/ CoordDie

\************************************************************************
\* Specification
\************************************************************************
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                     votes, voteSent, decisions, faulty, fwdTable>>

\************************************************************************
\* Safety invariant (Agreement)
\************************************************************************
TypeInvNB ==
    /\ decisions \in [ParticipantSet -> DecVals]
    /\ fwdTable \in [ParticipantSet -> [ParticipantSet -> FwdStatus]]
    /\ \A p,q \in ParticipantSet :
        (decisions[p] = commit /\ decisions[q] = abort) => FALSE

\************************************************************************
\* THEOREM (optional, not required by .cfg but useful)
\************************************************************************
THEOREM SpecImpliesInv == SpecNB => []TypeInvNB

====