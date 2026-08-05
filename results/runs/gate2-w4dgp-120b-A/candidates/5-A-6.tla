---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, cReq, cRecv, cSend, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, cReq, cRecv, cSend, cDecision, cAlive, cFaulty>>

AllRequested == \A p \in participants: cReq[p]
AllReceived == \A p \in participants: cRecv[p] # waiting
AllBroadcast == \A p \in participants: cSend[p] # notsent
AllVotedYes == \A p \in participants: pVote[p] = yes
SomeVotedNo == \Exists p \in participants: pVote[p] = no

TypeInv ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ cReq \in [participants -> BOOLEAN]
  /\ cRecv \in [participants -> {yes, no, waiting}]
  /\ cSend \in [participants -> {commit, abort, notsent}]
  /\ cDecision \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ pVote = [p \in participants |-> IF nondeterministicChoice THEN yes ELSE no]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSent = [p \in participants |-> FALSE]
  /\ cReq = [p \in participants |-> FALSE]
  /\ cRecv = [p \in participants |-> waiting]
  /\ cSend = [p \in participants |-> notsent]
  /\ cDecision = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

CoordSendReq(p) ==
  /\ cAlive
  /\ ~cReq[p]
  /\ cReq' = [cReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRecv, cSend, cDecision, cAlive, cFaulty>>

CoordReceiveVote(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ AllRequested
  /\ cRecv[p] = waiting
  /\ pSent[p]
  /\ cRecv' = [cRecv EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReq, cSend, cDecision, cAlive, cFaulty>>

CoordDetectFault(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ AllRequested
  /\ cRecv[p] = waiting
  /\ ~pAlive[p]
  /\ pFaulty[p]
  /\ cDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReq, cRecv, cSend, cAlive, cFaulty>>

CoordDecide ==
  /\ cAlive
  /\ cDecision = undecided
  /\ AllRequested
  /\ AllReceived
  /\ cDecision' = IF AllVotedYes THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReq, cRecv, cSend, cAlive, cFaulty>>

CoordBroadcast(p) ==
  /\ cAlive
  /\ cDecision # undecided
  /\ cSend[p] = notsent
  /\ cSend' = [cSend EXCEPT ![p] = cDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReq, cRecv, cDecision, cAlive, cFaulty>>

CoordDie ==
  /\ cAlive
  /\ ~cFaulty
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReq, cRecv, cSend, cDecision, cAlive, cFaulty>>

PartSendVote(p) ==
  /\ pAlive[p]
  /\ ~pFaulty[p]
  /\ cReq[p]
  /\ ~pSent[p]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, cReq, cRecv, cSend, cDecision, cAlive, cFaulty>>

PartAbortOnVote(p) ==
  /\ pAlive[p]
  /\ ~pFaulty[p]
  /\ pDecision[p] = undecided
  /\ pSent[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cReq, cRecv, cSend, cDecision, cAlive, cFaulty>>

PartAbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ ~pFaulty[p]
  /\ pDecision[p] = undecided
  /\ pSent[p]
  /\ ~cAlive
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cReq, cRecv, cSend, cDecision, cAlive, cFaulty>>

PartDecide(p) ==
  /\ pAlive[p]
  /\ ~pFaulty[p]
  /\ pDecision[p] = undecided
  /\ cSend[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = cSend[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cReq, cRecv, cSend, cDecision, cAlive, cFaulty>>

PartDie(p) ==
  /\ pAlive[p]
  /\ ~pFaulty[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSent, cReq, cRecv, cSend, cDecision, cAlive, cFaulty>>

Next ==
  \/ \E p \in participants: CoordSendReq(p)
  \/ \E p \in participants: CoordReceiveVote(p)
  \/ \E p \in participants: CoordDetectFault(p)
  \/ CoordDecide
  \/ \E p \in participants: CoordBroadcast(p)
  \/ CoordDie
  \/ \E p \in participants: PartSendVote(p)
  \/ \E p \in participants: PartAbortOnVote(p)
  \/ \E p \in participants: PartAbortOnTimeout(p)
  \/ \E p \in participants: PartDecide(p)
  \/ \E p \in participants: PartDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: CoordSendReq(p))
  /\ WF_vars(\E p \in participants: CoordDecide)
  /\ WF_vars(\E p \in participants: CoordBroadcast(p))
  /\ WF_vars(\E p \in participants: PartSendVote(p))
  /\ WF_vars(\E p \in participants: PartAbortOnVote(p))
  /\ WF_vars(\E p \in participants: PartAbortOnTimeout(p))
  /\ WF_vars(\E p \in participants: PartDecide(p))

Consistency == ~( \E p1 \in participants: pDecision[p1] = commit /\ \E p2 \in participants: pDecision[p2] = abort )
CommitValidity == \A p \in participants: pDecision[p] = commit => AllVotedYes
AbortValidity == \A p \in participants: pDecision[p] = abort => (SomeVotedNo \/ \E q \in participants: pFaulty[q] \/ cFaulty)
Irreversibility == (\A p \in participants: pDecision[p] = commit ~> pDecision[p] = commit) /\ (\A p \in participants: pDecision[p] = abort ~> pDecision[p] = abort)

Resolution ==
  <>( \A p \in participants: pDecision[p] # undecided \/ \E p \in participants: pFaulty[p] \/ cFaulty )

====