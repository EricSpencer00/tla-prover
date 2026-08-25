---- MODULE ACP_SB ----
EXTENDS FiniteSets, TLC

CONSTANTS  participants, yes, no, undecided, commit, abort, waiting, notsent

\* State variables
VARIABLES  pVote,          \* [participants -> {yes,no}]
           pAlive,         \* [participants -> BOOLEAN]
           pDecision,      \* [participants -> {undecided, commit, abort}]
           pSentVote,      \* [participants -> BOOLEAN]
           cAlive,         \* BOOLEAN
           cDecision,      \* {undecided, commit, abort}
           cRequested,     \* [participants -> BOOLEAN]
           cReceivedVote,  \* [participants -> {yes,no,waiting}]
           cBroadcasted    \* [participants -> {commit,abort,notsent}]

vars == << pVote, pAlive, pDecision, pSentVote,
          cAlive, cDecision, cRequested, cReceivedVote, cBroadcasted >>

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ cRequested = [p \in participants |-> FALSE]
    /\ cReceivedVote = [p \in participants |-> waiting]
    /\ cBroadcasted = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Coordinator actions

SendVoteRequest(p) ==
    /\ cAlive
    /\ ~cRequested[p]
    /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cDecision, cReceivedVote, cBroadcasted >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]      \* request already sent
    /\ cReceivedVote[p] = waiting
    /\ pAlive[p]          \* participant alive
    /\ pSentVote[p]       \* participant has sent its vote
    /\ cReceivedVote' = [cReceivedVote EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cDecision, cRequested, cBroadcasted >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]      \* request sent
    /\ cReceivedVote[p] = waiting
    /\ ~pAlive[p]         \* participant crashed before sending vote
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cRequested, cReceivedVote, cBroadcasted >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A q \in participants: cReceivedVote[q] # waiting
    /\ IF \A q \in participants: cReceivedVote[q] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cRequested, cReceivedVote, cBroadcasted >>

Broadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadcasted[p] = notsent
    /\ cBroadcasted' = [cBroadcasted EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cDecision, cRequested, cReceivedVote >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cDecision, cRequested, cReceivedVote, cBroadcasted >>

\* ----------------------------------------------------------------------
\* Participant actions

SendVote(p) ==
    /\ pAlive[p]
    /\ cRequested[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision,
                    cAlive, cDecision, cRequested, cReceivedVote, cBroadcasted >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cDecision, cRequested, cReceivedVote, cBroadcasted >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive                \* coordinator has died
    /\ ~cRequested[p]         \* no vote request ever sent to this participant
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cDecision, cRequested, cReceivedVote, cBroadcasted >>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cBroadcasted[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cBroadcasted[p]]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cDecision, cRequested, cReceivedVote, cBroadcasted >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << pVote, pDecision, pSentVote,
                    cAlive, cDecision, cRequested, cReceivedVote, cBroadcasted >>

\* ----------------------------------------------------------------------
\* Next-state relation

Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cRequested \in [participants -> BOOLEAN]
    /\ cReceivedVote \in [participants -> {yes, no, waiting}]
    /\ cBroadcasted \in [participants -> {commit, abort, notsent}]

====