---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent,
          cReqSent, cRecv, cSent, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent,
           cReqSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

TypeInv ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ cReqSent \in [participants -> BOOLEAN]
  /\ cRecv \in [participants -> {yes, no, waiting}]
  /\ cSent \in [participants -> {commit, abort, notsent}]
  /\ cDecision \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSent = [p \in participants |-> FALSE]
  /\ cReqSent = [p \in participants |-> FALSE]
  /\ cRecv = [p \in participants |-> waiting]
  /\ cSent = [p \in participants |-> notsent]
  /\ cDecision = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

CReq(p) ==
  /\ cAlive
  /\ ~cReqSent[p]
  /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 cRecv, cSent, cDecision, cAlive, cFaulty>>

CRecv(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ cReqSent[p]
  /\ cRecv[p] = waiting
  /\ pSent[p]
  /\ cRecv' = [cRecv EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 cReqSent, cSent, cDecision, cAlive, cFaulty>>

CDetectFault(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ cReqSent[p]
  /\ cRecv[p] = waiting
  /\ ~pAlive[p]
  /\ cDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 cReqSent, cRecv, cSent, cAlive, cFaulty>>

CMadeDecision ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A p \in participants : cRecv[p] # waiting
  /\ cDecision' = (IF \A p \in participants : cRecv[p] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 cReqSent, cRecv, cSent, cAlive, cFaulty>>

CBroadcast(p) ==
  /\ cAlive
  /\ cDecision # undecided
  /\ cSent[p] = notsent
  /\ cSent' = [cSent EXCEPT ![p] = cDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 cReqSent, cRecv, cDecision, cAlive, cFaulty>>

CDie ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 cReqSent, cRecv, cSent, cDecision, cAlive>>

PSendVote(p) ==
  /\ pAlive[p]
  /\ cReqSent[p]
  /\ ~pSent[p]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                 cReqSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

PAbortOnVote(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ pSent[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                 cReqSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

PAbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ ~cAlive
  /\ ~cReqSent[p]
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                 cReqSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

PDecideFromCoordinator(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ cSent[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = cSent[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                 cReqSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

PDie(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSent,
                 cReqSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

Next ==
  \/ \E p \in participants : CReq(p) \/ CRecv(p) \/ CDetectFault(p) \/ CBroadcast(p)
  \/ CMadeDecision
  \/ CDie
  \/ \E p \in participants : PSendVote(p) \/ PAbortOnVote(p) \/ PAbortOnTimeout(p) \/ PDecideFromCoordinator(p) \/ PDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : PSendVote(p))
        /\ WF_vars(\E p \in participants : PDecideFromCoordinator(p))
        /\ WF_vars(\E p \in participants : PAbortOnVote(p))
        /\ WF_vars(\E p \in participants : PAbortOnTimeout(p))
        /\ WF_vars(\E p \in participants : PDie(p))
        /\ WF_vars(CBroadcast(participants[1]))
        /\ WF_vars(CMadeDecision)

AC1 == \A a, b \in participants : ~(pDecision[a] = commit /\ pDecision[b] = abort)

AC2 == \A a \in participants : pDecision[a] = commit => \A b \in participants : pVote[b] = yes

AC3 == \A a \in participants : pDecision[a] = abort =>
         \/ \E b \in participants : pVote[b] = no
         \/ \E b \in participants : pFaulty[b]
         \/ cFaulty

AC4 == \A a \in participants :
         /\ (pDecision[a] = commit) ~> (pDecision[a] = commit)
         /\ (pDecision[a] = abort) ~> (pDecision[a] = abort)

AC5 == <>(\A p \in participants : pDecision[p] \in {commit, abort} \/ cFaulty \/ \E q \in participants : pFaulty[q])

Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC5

====