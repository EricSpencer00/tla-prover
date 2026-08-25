---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    pVote,          \* [participants -> {yes,no}]
    pAlive,         \* [participants -> BOOLEAN]
    pFaulty,        \* [participants -> BOOLEAN]
    pDecision,      \* [participants -> {undecided, commit, abort}]
    pSent,          \* [participants -> BOOLEAN]  \* has the participant sent its vote?
    
    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    cRequestSent,   \* [participants -> BOOLEAN]  \* coordinator sent vote request?
    cVoteReceived,  \* [participants -> {yes,no,waiting}]
    cBroadcastSent, \* [participants -> {commit,abort,notsent}]
    cDecision       \* {undecided, commit, abort}

vars == << pVote, pAlive, pFaulty, pDecision, pSent,
           cAlive, cFaulty, cRequestSent, cVoteReceived,
           cBroadcastSent, cDecision >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cRequestSent \in [participants -> BOOLEAN]
    /\ cVoteReceived \in [participants -> {yes, no, waiting}]
    /\ cBroadcastSent \in [participants -> {commit, abort, notsent}]
    /\ cDecision \in {undecided, commit, abort}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ \A p \in participants: pVote[p] \in {yes, no}
    /\ \A p \in participants: pAlive[p] = TRUE
    /\ \A p \in participants: pFaulty[p] = FALSE
    /\ \A p \in participants: pDecision[p] = undecided
    /\ \A p \in participants: pSent[p] = FALSE
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ \A p \in participants: cRequestSent[p] = FALSE
    /\ \A p \in participants: cVoteReceived[p] = waiting
    /\ \A p \in participants: cBroadcastSent[p] = notsent
    /\ cDecision = undecided

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteRequest(p) ==
    /\ cAlive
    /\ ~cRequestSent[p]
    /\ cRequestSent' = [cRequestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cVoteReceived,
                    cBroadcastSent, cDecision >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequestSent[p]
    /\ cVoteReceived[p] = waiting
    /\ pSent[p]
    /\ pAlive[p]
    /\ cVoteReceived' = [cVoteReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cRequestSent,
                    cBroadcastSent, cDecision >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequestSent[p]
    /\ cVoteReceived[p] = waiting
    /\ ~pAlive[p]               \* participant has died
    /\ ~pSent[p]                \* without having sent its vote
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cRequestSent,
                    cVoteReceived, cBroadcastSent >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cVoteReceived[p] # waiting
    /\ cDecision' = IF \A p \in participants: cVoteReceived[p] = yes
                    THEN commit
                    ELSE abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cRequestSent,
                    cVoteReceived, cBroadcastSent >>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadcastSent[p] = notsent
    /\ cBroadcastSent' = [cBroadcastSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cRequestSent,
                    cVoteReceived, cDecision >>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cRequestSent, cVoteReceived,
                    cBroadcastSent, cDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cRequestSent[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                    pDecision,
                    cAlive, cFaulty, cRequestSent,
                    cVoteReceived, cBroadcastSent, cDecision >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cRequestSent,
                    cVoteReceived, cBroadcastSent, cDecision >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cRequestSent[p]          \* coordinator died before sending request
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cRequestSent,
                    cVoteReceived, cBroadcastSent, cDecision >>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cBroadcastSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cBroadcastSent[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cRequestSent,
                    cVoteReceived, cBroadcastSent, cDecision >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSent,
                    cAlive, cFaulty, cRequestSent,
                    cVoteReceived, cBroadcastSent, cDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ CoordinatorDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant (already defined as TypeInv)
\* ----------------------------------------------------------------------
\* (The cfg file will refer to TypeInv)

====