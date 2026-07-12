---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pVote,          \* [p \in participants |-> {yes, no}]
    pAlive,         \* [p \in participants |-> BOOLEAN]
    pDecision,      \* [p \in participants |-> {undecided, commit, abort}]
    pFaulty,        \* [p \in participants |-> BOOLEAN]
    pSentVote,      \* [p \in participants |-> BOOLEAN]

    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    cDecision,      \* {undecided, commit, abort}
    cReqSent,       \* [p \in participants |-> BOOLEAN]
    cVoteReceived,  \* [p \in participants |-> {waiting, yes, no}]
    cBroadcastSent  \* [p \in participants |-> {notsent, commit, abort}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
UndecidedDecisions == {undecided}
AllYes(votes) == \A p \in participants : votes[p] = yes

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote = [p \in participants |-> CHOOSE v \in {yes, no} : v]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cReqSent = [p \in participants |-> FALSE]
    /\ cVoteReceived = [p \in participants |-> waiting]
    /\ cBroadcastSent = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteRequest(p) ==
    /\ cAlive
    /\ ~cReqSent[p]
    /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cDecision, cVoteReceived, cBroadcastSent >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[p]
    /\ cVoteReceived[p] = waiting
    /\ pSentVote[p]
    /\ cVoteReceived' = [cVoteReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cDecision, cReqSent, cBroadcastSent >>

DetectParticipantFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[p]
    /\ cVoteReceived[p] = waiting
    /\ ~pAlive[p]
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cReqSent, cVoteReceived, cBroadcastSent >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cVoteReceived[p] \in {yes, no}
    /\ IF \A p \in participants : cVoteReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cReqSent, cVoteReceived, cBroadcastSent >>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecision \in {commit, abort}
    /\ cBroadcastSent[p] = notsent
    /\ cBroadcastSent' = [cBroadcastSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cReqSent, cVoteReceived >>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cDecision, cReqSent, cVoteReceived, cBroadcastSent >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ cReqSent[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty,
                    cAlive, cFaulty, cDecision, cReqSent, cVoteReceived, cBroadcastSent >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                    cAlive, cFaulty, cDecision, cReqSent, cVoteReceived, cBroadcastSent, pSentVote >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                    cAlive, cFaulty, cDecision, cReqSent, cVoteReceived, cBroadcastSent, pSentVote >>

DecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cBroadcastSent[p] \in {commit, abort}
    /\ pDecision' = [pDecision EXCEPT ![p] = cBroadcastSent[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                    cAlive, cFaulty, cDecision, cReqSent, cVoteReceived, cBroadcastSent, pSentVote >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSentVote,
                    cAlive, cFaulty, cDecision, cReqSent, cVoteReceived, cBroadcastSent >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVoteRequest(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectParticipantFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordinatorDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< pVote, pAlive, pDecision, pFaulty, pSentVote,
                           cAlive, cFaulty, cDecision, cReqSent, cVoteReceived, cBroadcastSent >>

\* ----------------------------------------------------------------------
\* Type invariant (for TLC)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVoteReceived \in [participants -> {waiting, yes, no}]
    /\ cBroadcastSent \in [participants -> {notsent, commit, abort}]

\* ----------------------------------------------------------------------
\* Safety properties (not required by the .cfg but useful for TLC)
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants :
        (pDecision[p] = commit) => \A q \in participants : pVote[q] = yes

AbortValidity ==
    \A p \in participants :
        (pDecision[p] = abort) =>
            (\E q \in participants : pVote[q] = no) \/ (\E q \in participants : pFaulty[q]) \/ cFaulty

Irrevocability ==
    \A p \in participants :
        (pDecision[p] = commit) => pDecision[p] = commit
    /\ \A p \in participants :
        (pDecision[p] = abort) => pDecision[p] = abort

\* ----------------------------------------------------------------------
\* Liveness property (not required by the .cfg but useful for TLC)
\* ----------------------------------------------------------------------
DecideOrFault ==
    []<> (\A p \in participants : pDecision[p] \in {commit, abort}) \/ []<> cFaulty \/ []<> \E p \in participants : pFaulty[p]

====