---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pSentVote,
          cAlive, cFaulty, cRequestSent, cVoteReceived, cDecisionSent, cDecision

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cRequestSent \in [participants -> BOOLEAN]
    /\ cVoteReceived \in [participants -> {yes, no, waiting}]
    /\ cDecisionSent \in [participants -> {commit, abort, notsent}]
    /\ cDecision \in {undecided, commit, abort}
    /\ cFaulty = ~cAlive

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ \A p \in participants: pVote[p] \in {yes, no}
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cRequestSent = [p \in participants |-> FALSE]
    /\ cVoteReceived = [p \in participants |-> waiting]
    /\ cDecisionSent = [p \in participants |-> notsent]
    /\ cDecision = undecided
    /\ TypeInv

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ cAlive
    /\ ~cRequestSent[p]
    /\ cRequestSent' = [cRequestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                   cAlive, cFaulty, cVoteReceived, cDecisionSent, cDecision>>

CoordReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequestSent[p]
    /\ cVoteReceived[p] = waiting
    /\ pSentVote[p]
    /\ pAlive[p]
    /\ cVoteReceived' = [cVoteReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                   cAlive, cFaulty, cRequestSent, cDecisionSent, cDecision>>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequestSent[p]
    /\ cVoteReceived[p] = waiting
    /\ ~pAlive[p]
    /\ ~pSentVote[p]
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                   cAlive, cFaulty, cRequestSent, cVoteReceived, cDecisionSent>>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cVoteReceived[p] # waiting
    /\ IF \A p \in participants: cVoteReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                   cAlive, cFaulty, cRequestSent, cVoteReceived, cDecisionSent>>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cDecisionSent[p] = notsent
    /\ cDecisionSent' = [cDecisionSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                   cAlive, cFaulty, cRequestSent, cVoteReceived, cDecision>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                   cRequestSent, cVoteReceived, cDecisionSent, cDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ pAlive[p]
    /\ cRequestSent[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision,
                   cAlive, cFaulty, cRequestSent, cVoteReceived, cDecisionSent, cDecision>>

PartAbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pSentVote,
                   cAlive, cFaulty, cRequestSent, cVoteReceived, cDecisionSent, cDecision>>

PartAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cRequestSent[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pSentVote,
                   cAlive, cFaulty, cRequestSent, cVoteReceived, cDecisionSent, cDecision>>

PartDecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cDecisionSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecisionSent[p]]
    /\ UNCHANGED <<pVote, pAlive, pSentVote,
                   cAlive, cFaulty, cRequestSent, cVoteReceived, cDecisionSent, cDecision>>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pVote, pDecision, pSentVote,
                   cAlive, cFaulty, cRequestSent, cVoteReceived, cDecisionSent, cDecision>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_<<pVote, pAlive, pDecision, pSentVote,
                       cAlive, cFaulty, cRequestSent, cVoteReceived,
                       cDecisionSent, cDecision>>

====