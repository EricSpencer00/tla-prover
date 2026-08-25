---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* BOOLEAN: coordinator is alive
    coordDecision,       \* {undecided, commit, abort}
    requestSent,         \* [participants -> BOOLEAN]   (vote request sent?)
    receivedVote,        \* [participants -> {yes,no,waiting}]
    broadcastSent,       \* [participants -> {sent, notsent}]
    vote,                \* [participants -> {yes,no}]
    pAlive,              \* [participants -> BOOLEAN]   (participant alive)
    decided,             \* [participants -> {undecided, commit, abort}]
    sentVote             \* [participants -> BOOLEAN]   (vote already sent)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ requestSent \in [participants -> BOOLEAN]
    /\ receivedVote \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {sent, notsent}]
    /\ vote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ decided \in [participants -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ requestSent = [p \in participants |-> FALSE]
    /\ receivedVote = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ vote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ decided = [p \in participants |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendReq(p) ==
    /\ coordAlive
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, receivedVote,
                  broadcastSent, vote, pAlive, decided, sentVote>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent[p]
    /\ receivedVote[p] = waiting
    /\ sentVote[p]               \* participant has sent its vote
    /\ receivedVote' = [receivedVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent,
                  broadcastSent, vote, pAlive, decided, sentVote>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent[p]
    /\ receivedVote[p] = waiting
    /\ ~pAlive[p]                \* participant crashed before sending vote
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, requestSent, receivedVote,
                  broadcastSent, vote, pAlive, decided, sentVote>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : requestSent[p]            \* all requests sent
    /\ \A p \in participants : receivedVote[p] # waiting   \* all votes received
    /\ IF \A p \in participants : receivedVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, requestSent, receivedVote,
                  broadcastSent, vote, pAlive, decided, sentVote>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = sent]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent,
                  receivedVote, vote, pAlive, decided, sentVote>>

DieCoord ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, requestSent, receivedVote,
                  broadcastSent, vote, pAlive, decided, sentVote>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ requestSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent, receivedVote,
                  broadcastSent, vote, pAlive, decided>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ decided[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent, receivedVote,
                  broadcastSent, vote, pAlive, sentVote>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ decided[p] = undecided
    /\ ~coordAlive
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent, receivedVote,
                  broadcastSent, vote, pAlive, sentVote>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ decided[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ decided' = [decided EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent, receivedVote,
                  broadcastSent, vote, pAlive, sentVote>>

DieParticipant(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent, receivedVote,
                  broadcastSent, vote, decided, sentVote>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ DieCoord
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : DieParticipant(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordDecision, requestSent,
                 receivedVote, broadcastSent, vote,
                 pAlive, decided, sentVote>>

\* ----------------------------------------------------------------------
\* Invariant required by the configuration
\* ----------------------------------------------------------------------
THEOREM TypeInvariant == Spec => []TypeInv

====