---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*----------------------------------------------------------------------
\* CONSTANTS (to be bound in the .cfg)
\*----------------------------------------------------------------------
CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort, \* Decision values
    waiting, notsent          \* Communication status values

\*----------------------------------------------------------------------
\* State variables
\*----------------------------------------------------------------------
VARIABLES
    coordAlive,            \* TRUE iff the coordinator is alive
    coordFaulty,           \* TRUE iff the coordinator has crashed
    coordDecision,         \* coordinator's decision (undecided/commit/abort)
    coordRequested,        \* set of participants to which a vote request was sent
    coordReceived,         \* [p \in participants |-> waiting or yes/no]
    coordBroadcasted,      \* [p \in participants |-> notsent or commit/abort]

VARIABLES
    partAlive,             \* [p \in participants |-> BOOLEAN]
    partFaulty,            \* [p \in participants |-> BOOLEAN]
    partVote,              \* [p \in participants |-> yes/no]
    partDec,               \* [p \in participants |-> undecided/commit/abort]
    partSent               \* [p \in participants |-> BOOLEAN]  \* has the participant sent its vote?

\*----------------------------------------------------------------------
\* Helper definitions
\*----------------------------------------------------------------------
AllDecided ==
    \A p \in participants : partDec[p] # undecided

AllBroadcasted ==
    \A p \in participants : coordBroadcasted[p] # notsent

CoordHasReceivedAll ==
    \A p \in participants : coordReceived[p] # waiting

AllVotesYes ==
    \A p \in participants : partVote[p] = yes

SomeVoteNo ==
    \E p \in participants : partVote[p] = no

SomeParticipantFaulty ==
    \E p \in participants : partFaulty[p] = TRUE

\*----------------------------------------------------------------------
\* Initial state
\*----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordRequested = {}
    /\ coordReceived = [p \in participants |-> waiting]
    /\ coordBroadcasted = [p \in participants |-> notsent]

    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> IF RandomChoice({yes, no}) = 1 THEN yes ELSE no]
    /\ partDec = [p \in participants |-> undecided]
    /\ partSent = [p \in participants |-> FALSE]

\*----------------------------------------------------------------------
\* Actions
\*----------------------------------------------------------------------
\* Coordinator actions
CoordSendRequest ==
    /\ coordAlive
    /\ \E p \in participants \ {coordRequested} :
        /\ coordRequested' = coordRequested \cup {p}
        /\ UNCHANGED <<coordDecision, coordReceived, coordBroadcasted,
                        partAlive, partFaulty, partVote, partDec, partSent,
                        coordAlive, coordFaulty>>

CoordReceiveVote ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \E p \in participants :
        /\ p \in coordRequested
        /\ coordReceived[p] = waiting
        /\ partSent[p] = TRUE
        /\ coordReceived' = [coordReceived EXCEPT ![p] = partVote[p]]
        /\ UNCHANGED <<coordDecision, coordRequested, coordBroadcasted,
                        partAlive, partFaulty, partVote, partDec, partSent,
                        coordAlive, coordFaulty>>

CoordDetectFault ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \E p \in participants :
        /\ p \in coordRequested
        /\ coordReceived[p] = waiting
        /\ partAlive[p] = FALSE
        /\ coordDecision' = abort
        /\ coordBroadcasted' = [p \in participants |-> IF p = p THEN abort ELSE notsent]
        /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordReceived,
                        partAlive, partFaulty, partVote, partDec, partSent>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ CoordHasReceivedAll
    /\ IF AllVotesYes
          THEN /\ coordDecision' = commit
               /\ coordBroadcasted' = [p \in participants |-> IF p \in participants THEN commit ELSE notsent]
          ELSE /\ coordDecision' = abort
               /\ coordBroadcasted' = [p \in participants |-> IF p \in participants THEN abort ELSE notsent]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordReceived,
                    partAlive, partFaulty, partVote, partDec, partSent>>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants :
        /\ coordBroadcasted[p] = notsent
        /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![p] = coordDecision]
        /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                        coordReceived, partAlive, partFaulty, partVote, partDec, partSent>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordRequested, coordReceived, coordBroadcasted,
                    partAlive, partFaulty, partVote, partDec, partSent>>

\* Participant actions
PartSendVote ==
    /\ partAlive[self]
    /\ \E p \in participants :
        /\ p = self
        /\ p \in coordRequested
        /\ partSent[p] = FALSE
        /\ partSent' = [partSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                        coordReceived, coordBroadcasted,
                        partAlive, partFaulty, partVote, partDec>>

PartAbortOnVote ==
    /\ partAlive[self]
    /\ partDec[self] = undecided
    /\ partSent[self] = TRUE
    /\ partVote[self] = no
    /\ partDec' = [partDec EXCEPT ![self] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    partAlive, partFaulty, partVote, partSent>>

PartAbortOnTimeout ==
    /\ partAlive[self]
    /\ partDec[self] = undecided
    /\ coordAlive = FALSE
    /\ partDec' = [partDec EXCEPT ![self] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    partAlive, partFaulty, partVote, partSent>>

PartDecideFromCoord ==
    /\ partAlive[self]
    /\ partDec[self] = undecided
    /\ coordBroadcasted[self] # notsent
    /\ partDec' = [partDec EXCEPT ![self] = coordBroadcasted[self]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    partAlive, partFaulty, partVote, partSent>>

PartDie ==
    /\ partAlive[self]
    /\ partAlive' = [partAlive EXCEPT ![self] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![self] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    partVote, partDec, partSent>>

\*----------------------------------------------------------------------
\* Next-state relation
\*----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : CoordSendRequest /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReceived, coordBroadcasted,
                                                        partAlive, partFaulty, partVote, partDec, partSent>>
    \/ \E p \in participants : CoordReceiveVote /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested, coordBroadcasted,
                                                        partAlive, partFaulty, partVote, partDec, partSent>>
    \/ \E p \in participants : CoordDetectFault /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordReceived,
                                                        partAlive, partFaulty, partVote, partDec, partSent>>
    \/ CoordMakeDecision
    \/ \E p \in participants : CoordBroadcast
    \/ CoordDie
    \/ \E self \in participants : PartSendVote
    \/ \E self \in participants : PartAbortOnVote
    \/ \E self \in participants : PartAbortOnTimeout
    \/ \E self \in participants : PartDecideFromCoord
    \/ \E self \in participants : PartDie

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision, coordRequested,
                     coordReceived, coordBroadcasted,
                     partAlive, partFaulty, partVote, partDec, partSent>>

\*----------------------------------------------------------------------
\* Type invariant (helps TLC but is not the safety invariant)
\*----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordRequested \subseteq participants
    /\ coordReceived \in [participants -> {waiting, yes, no}]
    /\ coordBroadcasted \in [participants -> {notsent, commit, abort}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> {yes, no}]
    /\ partDec \in [participants -> {undecided, commit, abort}]
    /\ partSent \in [participants -> BOOLEAN]

\*----------------------------------------------------------------------
\* Safety invariant AC1 (Agreement) – cannot have one commit and one abort
\*----------------------------------------------------------------------
Safety_AC1 ==
    \A p, q \in participants :
        ~(partDec[p] = commit /\ partDec[q] = abort)

\*----------------------------------------------------------------------
\* THEOREM (optional, not required by the cfg but useful)
\*----------------------------------------------------------------------
THEOREM Spec => []Safety_AC1

\*----------------------------------------------------------------------
\* Additional invariants (not required by cfg)
\*----------------------------------------------------------------------
(* AC2, AC3, AC4 could be added similarly if desired *)

\*----------------------------------------------------------------------
\* END MODULE
\*----------------------------------------------------------------------
====