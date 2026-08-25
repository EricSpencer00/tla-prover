---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    pVote,          \* participants' votes (yes/no)
    pAlive,         \* participants' aliveness
    pFaulty,        \* participants' fault status
    pDecision,      \* participants' final decision (undecided/commit/abort)
    pSent,          \* whether a participant has sent its vote
    cAlive,         \* coordinator aliveness
    cFaulty,        \* coordinator fault status
    cSentReq,       \* whether a vote request has been sent to a participant
    cReceived,      \* votes received from participants (yes/no/waiting)
    cDecision,      \* coordinator's decision (undecided/commit/abort)
    cSentDec        \* whether the decision has been broadcast to a participant

vars == << pVote, pAlive, pFaulty, pDecision, pSent,
          cAlive, cFaulty, cSentReq, cReceived, cDecision, cSentDec >>

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
    /\ cSentReq \in [participants -> BOOLEAN]
    /\ cReceived \in [participants -> ({yes, no} \cup {waiting})]
    /\ cDecision \in {undecided, commit, abort}
    /\ cSentDec \in [participants -> {sent, notsent}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ \A p \in participants:
          /\ pVote[p] \in {yes, no}
          /\ pAlive[p] = TRUE
          /\ pFaulty[p] = FALSE
          /\ pDecision[p] = undecided
          /\ pSent[p] = FALSE
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cSentReq = [p \in participants |-> FALSE]
    /\ cReceived = [p \in participants |-> waiting]
    /\ cDecision = undecided
    /\ cSentDec = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ cAlive
    /\ ~cSentReq[p]
    /\ cSentReq' = [cSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cReceived, cDecision, cSentDec >>

CoordReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cSentReq[p]
    /\ cReceived[p] = waiting
    /\ pSent[p]                 \* participant has already sent its vote
    /\ cReceived' = [cReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cSentReq, cDecision, cSentDec >>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cSentReq[p]
    /\ cReceived[p] = waiting
    /\ ~pAlive[p]               \* participant crashed
    /\ ~pSent[p]                \* and never sent its vote
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cSentReq, cReceived, cSentDec >>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A q \in participants: cReceived[q] # waiting
    /\ IF \A q \in participants: cReceived[q] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cSentReq, cReceived, cSentDec >>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSentDec[p] = notsent
    /\ cSentDec' = [cSentDec EXCEPT ![p] = sent]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cAlive, cFaulty, cSentReq, cReceived, cDecision >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                    cSentReq, cReceived, cDecision, cSentDec >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ pAlive[p]
    /\ cSentReq[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    cAlive, cFaulty, cSentReq, cReceived, cDecision, cSentDec >>

PartAbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cSentReq, cReceived, cDecision, cSentDec >>

PartAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive                \* coordinator crashed
    /\ ~cSentReq[p]           \* and never sent a request to this participant
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cSentReq, cReceived, cDecision, cSentDec >>

PartDecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSentDec[p] = sent
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cSentReq, cReceived, cDecision, cSentDec >>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSent,
                    cAlive, cFaulty, cSentReq, cReceived, cDecision, cSentDec >>

\* ----------------------------------------------------------------------
\* Progress actions (excluding death)
\* ----------------------------------------------------------------------
CoordProgress ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)

PartProgress ==
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)

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
Spec == Init /\ [][Next]_vars /\ WF_vars(CoordProgress) /\ WF_vars(PartProgress)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
INVARIANT TypeInv

====