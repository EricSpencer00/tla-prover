---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pVote,           \* [p \in participants |-> yes/no]
          pAlive,          \* [p \in participants |-> BOOLEAN]
          pDecision,       \* [p \in participants |-> {undecided, commit, abort}]
          pFaulty,         \* [p \in participants |-> BOOLEAN]  (crashed)
          pSent,           \* [p \in participants |-> BOOLEAN]  (vote sent)
          cRequest,        \* [p \in participants |-> BOOLEAN]  (vote request sent)
          cVoteRecv,       \* [p \in participants |-> {yes, no, waiting}]
          cBroadcast,      \* [p \in participants |-> {sent, notsent}]
          cDecision,       \* {undecided, commit, abort}
          cAlive,          \* BOOLEAN
          cFaulty          \* BOOLEAN

vars == << pVote, pAlive, pDecision, pFaulty, pSent,
           cRequest, cVoteRecv, cBroadcast, cDecision,
           cAlive, cFaulty >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ cRequest = [p \in participants |-> FALSE]
    /\ cVoteRecv = [p \in participants |-> waiting]
    /\ cBroadcast = [p \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ cAlive /\ ~cFaulty
    /\ ~cRequest[p]
    /\ cRequest' = [cRequest EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSent,
                    cVoteRecv, cBroadcast, cDecision, cFaulty >>

CoordRecvVote(p) ==
    /\ cAlive /\ ~cFaulty
    /\ cDecision = undecided
    /\ cRequest[p]                     \* request already sent
    /\ cVoteRecv[p] = waiting
    /\ pSent[p]                        \* participant has sent its vote
    /\ cVoteRecv' = [cVoteRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSent,
                    cRequest, cBroadcast, cDecision, cFaulty >>

CoordDetectFault(p) ==
    /\ cAlive /\ ~cFaulty
    /\ cDecision = undecided
    /\ cRequest[p]
    /\ cVoteRecv[p] = waiting
    /\ ~pAlive[p]                      \* participant dead
    /\ pFaulty[p]                      \* and marked faulty
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSent,
                    cRequest, cVoteRecv, cBroadcast, cFaulty,
                    cAlive >>

CoordMakeDecision ==
    /\ cAlive /\ ~cFaulty
    /\ cDecision = undecided
    /\ \A p \in participants: cVoteRecv[p] # waiting
    /\ IF \A p \in participants: cVoteRecv[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSent,
                    cRequest, cVoteRecv, cBroadcast, cFaulty,
                    cAlive >>

CoordBroadcast(p) ==
    /\ cAlive /\ ~cFaulty
    /\ cDecision # undecided
    /\ cBroadcast[p] = notsent
    /\ cBroadcast' = [cBroadcast EXCEPT ![p] = sent]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSent,
                    cRequest, cVoteRecv, cDecision, cFaulty,
                    cAlive >>

CoordDie ==
    /\ cAlive /\ ~cFaulty
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSent,
                    cRequest, cVoteRecv, cBroadcast, cDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ pAlive[p] /\ ~pFaulty[p]
    /\ cRequest[p]                     \* request received
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty,
                    cRequest, cVoteRecv, cBroadcast, cDecision,
                    cAlive, cFaulty >>

PartAbortOnVote(p) ==
    /\ pAlive[p] /\ ~pFaulty[p]
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision[p] = undecided
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cRequest, cVoteRecv, cBroadcast, cDecision,
                    cAlive, cFaulty >>

PartAbortOnTimeout(p) ==
    /\ pAlive[p] /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive                         \* coordinator dead
    /\ ~cRequest[p]                    \* no request ever arrived
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cRequest, cVoteRecv, cBroadcast, cDecision,
                    cAlive, cFaulty >>

PartDecideOnBroadcast(p) ==
    /\ pAlive[p] /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ cBroadcast[p] = sent
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                    cRequest, cVoteRecv, cBroadcast,
                    cDecision, cAlive, cFaulty >>

PartDie(p) ==
    /\ pAlive[p] /\ ~pFaulty[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSent,
                    cRequest, cVoteRecv, cBroadcast, cDecision,
                    cAlive, cFaulty >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
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
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cRequest \in [participants -> BOOLEAN]
    /\ cVoteRecv \in [participants -> {yes, no, waiting}]
    /\ cBroadcast \in [participants -> {sent, notsent}]
    /\ cDecision \in {undecided, commit, abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ \A p \in participants: (pFaulty[p] => ~pAlive[p])
    /\ (cFaulty => ~cAlive)

====