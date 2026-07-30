---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-Blocking Atomic Commitment Protocol (ACP-NB): exactly one decision per
\* run, decided by forwarding rather than by a single coordinator broadcast.
\* Extends the simple broadcast variant by having every participant forward
\* its pre-decision to all others before finalizing locally; this guarantees
\* that no non-faulty participant is left waiting forever.
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty, txTbl

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty, txTbl>>

TypeInvNB ==
  /\ pVote \in [participants -> {yes, no, waiting}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ cState \in {waiting, collecting, decided, dead}
  /\ cReq \in {yes, no, waiting}
  /\ cVote \in {yes, no, waiting}
  /\ cDecision \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN
  /\ txTbl \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pVote = [p \in participants |-> waiting]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSent = [p \in participants |-> FALSE]
  /\ cState = waiting
  /\ cReq = waiting
  /\ cVote = waiting
  /\ cDecision = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE
  /\ txTbl = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions (inherited from the base variant):
SendRequest ==
  /\ cState = waiting
  /\ cAlive
  /\ cState' = collecting
  /\ cReq' = yes
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cState, cVote, cDecision, cAlive, cFaulty, txTbl>>

GetVote(p) ==
  /\ cState = collecting
  /\ cAlive
  /\ pAlive[p]
  /\ ~pSent[p]
  /\ pVote' = [pVote EXCEPT ![p] = cReq]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pAlive, pDecision, pFaulty, cState, cReq, cVote, cDecision, cAlive, cFaulty, txTbl>>

DetectFault(p) ==
  /\ cState = collecting
  /\ pAlive[p]
  /\ ~pSent[p]
  /\ pVote' = [pVote EXCEPT ![p] = no]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pAlive, pDecision, pFaulty, cState, cReq, cVote, cDecision, cAlive, cFaulty, txTbl>>

MakeDecision ==
  /\ cState = collecting
  /\ cAlive
  /\ cReq \in {yes, no}
  /\ cDecision' = IF cReq = no THEN abort ELSE commit
  /\ cState' = decided
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReq, cVote, cAlive, cFaulty, txTbl>>

BroadcastDecision ==
  /\ cState = decided
  /\ cAlive
  /\ \E p \in participants :
       /\ txTbl[p][p] = notsent
       /\ txTbl' = [txTbl EXCEPT ![p][p] = cDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty>>

CoordinatorDies ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cState, cReq, cVote, cDecision, txTbl>>

\* New / modified participant actions (reliable broadcast):
PreDecideFromCoordinator(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ txTbl[p][p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = txTbl[p][p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty, txTbl>>

PreDecideFromForward(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ \E q \in participants :
       /\ q # p
       /\ txTbl[q][p] # notsent
       /\ pDecision' = [pDecision EXCEPT ![p] = txTbl[q][p]]
       /\ UNCHANGED txTbl
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty>>

Forward(p, q) ==
  /\ pAlive[p]
  /\ q # p
  /\ pDecision[p] # undecided
  /\ txTbl[p][q] = notsent
  /\ txTbl' = [txTbl EXCEPT ![p][q] = pDecision[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty>>

Decide ==
  /\ \E p \in participants :
       /\ pAlive[p]
       /\ \A q \in participants : txTbl[p][q] # notsent
       /\ pDecision[p] # undecided
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty, txTbl>>

AbortOnTimeout ==
  /\ \E p \in participants :
       /\ pAlive[p]
       /\ pDecision[p] = undecided
       /\ ~cAlive
       /\ (\A q \in participants : txTbl[q][p] = notsent)
       /\ (\A q \in participants : ~pAlive[q] \/ txTbl[q][p] = notsent)
       /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty, txTbl>>

Die(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSent, cState, cReq, cVote, cDecision, cAlive, cFaulty, txTbl>>

Next ==
  \/ SendRequest \/ MakeDecision \/ BroadcastDecision \/ CoordinatorDies
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ PreDecideFromCoordinator(p) \/ PreDecideFromForward(p) \/ Decide \/ AbortOnTimeout \/ Die(p)
  \/ \E p, q \in participants : Forward(p, q)

Fairness ==
  /\ \A p \in participants :
       /\ WF_vars(\E q \in participants : Forward(p, q))
       /\ WF_vars(PreDecideFromCoordinator(p))
       /\ WF_vars(PreDecideFromForward(p))
       /\ WF_vars(Die(p))
  /\ SF_vars(SendRequest)
  /\ SF_vars(MakeDecision)
  /\ SF_vars(BroadcastDecision)
  /\ SF_vars(CoordinatorDies)

SpecNB == Init /\ [][Next]_vars /\ Fairness

\* Safety: no two participants reach different decisions, and any decision is
\* backed by unanimous yes or a detected fault.
AC1 == \A p, q \in participants : (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE
AC2 == \A p \in participants : pDecision[p] = commit => \A q \in participants : pVote[q] = yes
AC3 == \A p \in participants : pDecision[p] = abort => (\E q \in participants : pVote[q] = no \/ pFaulty[q] \/ cFaulty)
AC4 == \A p \in participants : (pDecision[p] = commit \/ pDecision[p] = abort) ~> pDecision[p]

\* Liveness: every non-faulty participant eventually reaches a decision.
AC3Liveness == <>(\A p \in participants : pDecision[p] # undecided \/ pFaulty[p] \/ cFaulty)
AC5 == \A p \in participants : (pAlive[p] /\ pDecision[p] = undecided) ~> (pDecision[p] # undecided \/ pFaulty[p])

Properties == AC3Liveness /\ AC5

====