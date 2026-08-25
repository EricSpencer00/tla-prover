---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pSentVote,
          cAlive, cFaulty, cRequested, cVoteReceived, cDecision, cSentDecision

\* ----------------------------------------------------------------------
\* Types
VoteSet      == {yes, no}
DecisionSet  == {undecided, commit, abort}
BoolSet      == BOOLEAN

\* ----------------------------------------------------------------------
\* Type invariant
TypeInv ==
    /\ pVote          \in [participants -> VoteSet]
    /\ pAlive         \in [participants -> BoolSet]
    /\ pDecision      \in [participants -> DecisionSet]
    /\ pSentVote      \in [participants -> BoolSet]
    /\ cAlive         \in BoolSet
    /\ cFaulty        \in BoolSet
    /\ cRequested     \in [participants -> BoolSet]
    /\ cVoteReceived  \in [participants -> (VoteSet \cup {waiting})]
    /\ cDecision      \in DecisionSet
    /\ cSentDecision  \in [participants -> BoolSet]   \* TRUE means decision sent

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ pVote          \in [participants -> VoteSet]   \* nondeterministic votes
    /\ pAlive         = [p \in participants |-> TRUE]
    /\ pDecision      = [p \in participants |-> undecided]
    /\ pSentVote      = [p \in participants |-> FALSE]
    /\ cAlive         = TRUE
    /\ cFaulty        = FALSE
    /\ cRequested     = [p \in participants |-> FALSE]
    /\ cVoteReceived  = [p \in participants |-> waiting]
    /\ cDecision      = undecided
    /\ cSentDecision  = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Coordinator actions
CoordSendReq(p) ==
    /\ cAlive
    /\ ~cRequested[p]
    /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cVoteReceived, cDecision, cSentDecision>>

CoordRecvVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cVoteReceived[p] = waiting
    /\ pSentVote[p]
    /\ cVoteReceived' = [cVoteReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cRequested, cDecision, cSentDecision>>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cVoteReceived[p] = waiting
    /\ ~pAlive[p]
    /\ ~pSentVote[p]
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cRequested, cVoteReceived, cSentDecision>>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cVoteReceived[p] # waiting
    /\ IF \A p \in participants: cVoteReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cRequested, cVoteReceived, cSentDecision>>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ ~cSentDecision[p]
    /\ cSentDecision' = [cSentDecision EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cRequested, cVoteReceived, cDecision>>

CoordDie ==
    /\ cAlive
    /\ cAlive'   = FALSE
    /\ cFaulty'  = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pSentVote,
                    cRequested, cVoteReceived, cDecision, cSentDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
PartSendVote(p) ==
    /\ pAlive[p]
    /\ cRequested[p]          \* request has been received
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision,
                    cAlive, cFaulty, cRequested, cVoteReceived,
                    cDecision, cSentDecision>>

PartAbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pSentVote,
                    cAlive, cFaulty, cRequested, cVoteReceived,
                    cDecision, cSentDecision>>

PartAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cRequested[p]        \* no request arrived before coordinator died
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pSentVote,
                    cAlive, cFaulty, cRequested, cVoteReceived,
                    cDecision, cSentDecision>>

PartDecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSentDecision[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pSentVote,
                    cAlive, cFaulty, cRequested, cVoteReceived,
                    cDecision, cSentDecision>>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pVote, pDecision, pSentVote,
                    cAlive, cFaulty, cRequested, cVoteReceived,
                    cDecision, cSentDecision>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordRecvVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideOnBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
vars == <<pVote, pAlive, pDecision, pSentVote,
          cAlive, cFaulty, cRequested, cVoteReceived, cDecision, cSentDecision>>

Spec == Init /\ [][Next]_vars

====