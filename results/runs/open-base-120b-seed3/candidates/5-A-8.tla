---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,               \* BOOLEAN
    coordDecision,            \* {undecided, commit, abort}
    coordReqSent,             \* [participants -> BOOLEAN]
    coordVotes,               \* [participants -> {yes,no,waiting}]
    coordBroadcastSent,       \* [participants -> {notsent, commit, abort}]
    partAlive,                \* [participants -> BOOLEAN]
    partVote,                 \* [participants -> {yes,no}]
    partDecision,             \* [participants -> {undecided, commit, abort}]
    partSentVote              \* [participants -> BOOLEAN]

vars == << coordAlive, coordDecision, coordReqSent, coordVotes,
           coordBroadcastSent, partAlive, partVote,
           partDecision, partSentVote >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordReqSent \in [participants -> BOOLEAN]
    /\ coordVotes \in [participants -> {yes, no, waiting}]
    /\ coordBroadcastSent \in [participants -> {notsent, commit, abort}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> {yes, no}]
    /\ partDecision \in [participants -> {undecided, commit, abort}]
    /\ partSentVote \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordReqSent = [p \in participants |-> FALSE]
    /\ coordVotes = [p \in participants |-> waiting]
    /\ coordBroadcastSent = [p \in participants |-> notsent]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partDecision = [p \in participants |-> undecided]
    /\ partSentVote = [p \in participants |-> FALSE]
    /\ partVote \in [participants -> {yes, no}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CoordSendReq ==
    \E p \in participants:
        /\ coordAlive
        /\ ~coordReqSent[p]
        /\ coordReqSent' = [coordReqSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<coordAlive, coordDecision, coordVotes,
                       coordBroadcastSent, partAlive, partVote,
                       partDecision, partSentVote>>

CoordReceiveVote ==
    \E p \in participants:
        /\ coordAlive
        /\ coordDecision = undecided
        /\ coordReqSent[p]               \* request already sent
        /\ coordVotes[p] = waiting
        /\ partAlive[p]                  \* participant alive
        /\ partSentVote[p]               \* participant has sent its vote
        /\ coordVotes' = [coordVotes EXCEPT ![p] = partVote[p]]
        /\ UNCHANGED <<coordAlive, coordDecision, coordReqSent,
                       coordBroadcastSent, partAlive, partVote,
                       partDecision, partSentVote>>

CoordDetectFault ==
    \E p \in participants:
        /\ coordAlive
        /\ coordDecision = undecided
        /\ coordReqSent[p]
        /\ coordVotes[p] = waiting
        /\ ~partAlive[p]                 \* participant faulty
        /\ coordDecision' = abort
        /\ UNCHANGED <<coordAlive, coordReqSent, coordVotes,
                       coordBroadcastSent, partAlive, partVote,
                       partDecision, partSentVote>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordVotes[p] # waiting
    /\ IF \A p \in participants: coordVotes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordReqSent, coordVotes,
                   coordBroadcastSent, partAlive, partVote,
                   partDecision, partSentVote>>

CoordBroadcast ==
    \E p \in participants:
        /\ coordAlive
        /\ coordDecision \in {commit, abort}
        /\ coordBroadcastSent[p] = notsent
        /\ coordBroadcastSent' = [coordBroadcastSent EXCEPT ![p] = coordDecision]
        /\ UNCHANGED <<coordAlive, coordDecision, coordReqSent,
                       coordVotes, partAlive, partVote,
                       partDecision, partSentVote>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, coordReqSent, coordVotes,
                   coordBroadcastSent, partAlive, partVote,
                   partDecision, partSentVote>>

PartSendVote ==
    \E p \in participants:
        /\ partAlive[p]
        /\ coordReqSent[p]               \* has received request
        /\ ~partSentVote[p]
        /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<coordAlive, coordDecision, coordReqSent,
                       coordVotes, coordBroadcastSent,
                       partAlive, partVote, partDecision>>

PartAbortOnVote ==
    \E p \in participants:
        /\ partAlive[p]
        /\ partDecision[p] = undecided
        /\ partSentVote[p]
        /\ partVote[p] = no
        /\ partDecision' = [partDecision EXCEPT ![p] = abort]
        /\ UNCHANGED <<coordAlive, coordDecision, coordReqSent,
                       coordVotes, coordBroadcastSent,
                       partAlive, partVote, partSentVote>>

PartAbortOnTimeout ==
    \E p \in participants:
        /\ partAlive[p]
        /\ partDecision[p] = undecided
        /\ ~coordAlive                 \* coordinator has died
        /\ ~coordReqSent[p]            \* no request was ever sent
        /\ partDecision' = [partDecision EXCEPT ![p] = abort]
        /\ UNCHANGED <<coordAlive, coordDecision, coordReqSent,
                       coordVotes, coordBroadcastSent,
                       partAlive, partVote, partSentVote>>

PartDecideOnBroadcast ==
    \E p \in participants:
        /\ partAlive[p]
        /\ partDecision[p] = undecided
        /\ coordBroadcastSent[p] # notsent
        /\ partDecision' = [partDecision EXCEPT ![p] = coordBroadcastSent[p]]
        /\ UNCHANGED <<coordAlive, coordDecision, coordReqSent,
                       coordVotes, coordBroadcastSent,
                       partAlive, partVote, partSentVote>>

PartDie ==
    \E p \in participants:
        /\ partAlive[p]
        /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
        /\ UNCHANGED <<coordAlive, coordDecision, coordReqSent,
                       coordVotes, coordBroadcastSent,
                       partVote, partDecision, partSentVote>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordSendReq
    \/ PartSendVote
    \/ CoordReceiveVote
    \/ CoordDetectFault
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ PartAbortOnVote
    \/ PartAbortOnTimeout
    \/ PartDecideOnBroadcast
    \/ PartDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
INVARIANTS == TypeInv

=============================================================================