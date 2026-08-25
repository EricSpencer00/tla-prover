---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    pAlive,          \* [p \in participants -> BOOLEAN]
    pFaulty,         \* [p \in participants -> BOOLEAN]
    pVote,           \* [p \in participants -> {yes,no}]
    pSent,           \* [p \in participants -> BOOLEAN]
    pDecision,       \* [p \in participants -> {commit,abort,undecided}]
    cAlive,          \* BOOLEAN
    cFaulty,         \* BOOLEAN
    requestSent,     \* [p \in participants -> BOOLEAN]
    voteReceived,    \* [p \in participants -> {yes,no,waiting}]
    decisionSent,    \* [p \in participants -> {commit,abort,notsent}]
    cDecision        \* {commit,abort,undecided}

vars == << pAlive, pFaulty, pVote, pSent, pDecision,
           cAlive, cFaulty, requestSent, voteReceived, decisionSent, cDecision >>

Init ==
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ \A p \in participants:
        /\ pAlive[p] = TRUE
        /\ pFaulty[p] = FALSE
        /\ pVote[p] \in {yes, no}
        /\ pSent[p] = FALSE
        /\ pDecision[p] = undecided
        /\ requestSent[p] = FALSE
        /\ voteReceived[p] = waiting
        /\ decisionSent[p] = notsent

\* ---------- Coordinator actions ----------
SendReq(p) ==
    /\ cAlive = TRUE
    /\ requestSent[p] = FALSE
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent, pDecision,
                   cAlive, cFaulty, voteReceived, decisionSent, cDecision >>

RecvVote(p) ==
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ requestSent[p] = TRUE
    /\ voteReceived[p] = waiting
    /\ pSent[p] = TRUE
    /\ voteReceived' = [voteReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent, pDecision,
                   cAlive, cFaulty, requestSent, decisionSent, cDecision >>

DetectFault(p) ==
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ requestSent[p] = TRUE
    /\ voteReceived[p] = waiting
    /\ pAlive[p] = FALSE
    /\ pFaulty[p] = TRUE
    /\ cDecision' = abort
    /\ decisionSent' = [decisionSent EXCEPT ![q \in participants] = abort]
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent, pDecision,
                   cAlive, cFaulty, requestSent, voteReceived >>

MakeDecision ==
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ \A p \in participants: voteReceived[p] # waiting
    /\ IF \A p \in participants: voteReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent, pDecision,
                   cAlive, cFaulty, requestSent, voteReceived, decisionSent >>

Broadcast(p) ==
    /\ cAlive = TRUE
    /\ cDecision # undecided
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent, pDecision,
                   cAlive, cFaulty, requestSent, voteReceived, cDecision >>

CoordDie ==
    /\ cAlive = TRUE
    /\ cFaulty' = TRUE
    /\ cAlive' = FALSE
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent, pDecision,
                   requestSent, voteReceived, decisionSent, cDecision >>

\* ---------- Participant actions ----------
SendVote(p) ==
    /\ pAlive[p] = TRUE
    /\ requestSent[p] = TRUE
    /\ pSent[p] = FALSE
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pAlive, pFaulty, pVote, pDecision,
                   cAlive, cFaulty, requestSent, voteReceived,
                   decisionSent, cDecision >>

AbortOnNo(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ pSent[p] = TRUE
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent,
                   cAlive, cFaulty, requestSent, voteReceived,
                   decisionSent, cDecision >>

AbortOnTimeout(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ cAlive = FALSE
    /\ requestSent[p] = FALSE
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent,
                   cAlive, cFaulty, requestSent, voteReceived,
                   decisionSent, cDecision >>

DecideFromBroadcast(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ decisionSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED << pAlive, pFaulty, pVote, pSent,
                   cAlive, cFaulty, requestSent, voteReceived,
                   decisionSent, cDecision >>

PartDie(p) ==
    /\ pAlive[p] = TRUE
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << pVote, pSent, pDecision,
                   cAlive, cFaulty, requestSent, voteReceived,
                   decisionSent, cDecision >>

\* ---------- Next ----------
Next ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: RecvVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnNo(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ---------- Type invariant ----------
TypeInv ==
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {commit, abort, undecided}
    /\ \A p \in participants:
        /\ pAlive[p] \in BOOLEAN
        /\ pFaulty[p] \in BOOLEAN
        /\ pVote[p] \in {yes, no}
        /\ pSent[p] \in BOOLEAN
        /\ pDecision[p] \in {commit, abort, undecided}
        /\ requestSent[p] \in BOOLEAN
        /\ voteReceived[p] \in {yes, no, waiting}
        /\ decisionSent[p] \in {commit, abort, notsent}

Spec == Init /\ [][Next]_vars

====