---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, cReqd, cRecv, cSent, cDecision, cAlive, cFaulty

Rec == [participants -> {waiting} \union {yes, no}]
Dflt == [participants |-> waiting]

TypeOK ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ cReqd \in [participants -> BOOLEAN]
  /\ cRecv \in [participants -> {waiting} \union {yes, no}]
  /\ cSent \in [participants -> {notsent, commit, abort}]
  /\ cDecision \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = [pa \in participants |-> TRUE]
  /\ pDecision = [pa \in participants |-> undecided]
  /\ pFaulty = [pa \in participants |-> FALSE]
  /\ pSent = [pa \in participants |-> FALSE]
  /\ cReqd = [pa \in participants |-> FALSE]
  /\ cRecv = Dflt
  /\ cSent = [pa \in participants |-> notsent]
  /\ cDecision = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

SendVoteReq(pa) ==
  /\ cAlive = TRUE
  /\ cReqd[pa] = FALSE
  /\ cReqd' = [cReqd EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

ReceiveVote(pa) ==
  /\ cAlive = TRUE
  /\ cDecision = undecided
  /\ cReqd[pa] = TRUE
  /\ cRecv[pa] = waiting
  /\ pSent[pa] = TRUE
  /\ cRecv' = [cRecv EXCEPT ![pa] = pVote[pa]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReqd, cSent, cDecision, cAlive, cFaulty>>

DetectFault(pa) ==
  /\ cAlive = TRUE
  /\ cDecision = undecided
  /\ cReqd[pa] = TRUE
  /\ cRecv[pa] = waiting
  /\ pAlive[pa] = FALSE
  /\ cDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReqd, cRecv, cSent, cAlive, cFaulty>>

MakeDecision ==
  /\ cAlive = TRUE
  /\ cDecision = undecided
  /\ \A pa \in participants : cRecv[pa] # waiting
  /\ cDecision' = IF \A pa \in participants : cRecv[pa] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReqd, cRecv, cSent, cAlive, cFaulty>>

BroadcastDecision(pa) ==
  /\ cAlive = TRUE
  /\ cDecision # undecided
  /\ cSent[pa] = notsent
  /\ cSent' = [cSent EXCEPT ![pa] = cDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReqd, cRecv, cDecision, cAlive, cFaulty>>

DieCoordinator ==
  /\ cAlive = TRUE
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReqd, cRecv, cSent, cDecision>>

SendVote(pa) ==
  /\ pAlive[pa] = TRUE
  /\ cReqd[pa] = TRUE
  /\ pSent[pa] = FALSE
  /\ pSent' = [pSent EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, cReqd, cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortOnVote(pa) ==
  /\ pAlive[pa] = TRUE
  /\ pDecision[pa] = undecided
  /\ pSent[pa] = TRUE
  /\ pVote[pa] = no
  /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cReqd, cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortTimeoutReq(pa) ==
  /\ pAlive[pa] = TRUE
  /\ pDecision[pa] = undecided
  /\ cAlive = FALSE
  /\ cReqd[pa] = FALSE
  /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cReqd, cRecv, cSent, cDecision, cAlive, cFaulty>>

DecideFromBroadcast(pa) ==
  /\ pAlive[pa] = TRUE
  /\ pDecision[pa] = undecided
  /\ cSent[pa] # notsent
  /\ pDecision' = [pDecision EXCEPT ![pa] = cSent[pa]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cReqd, cRecv, cSent, cDecision, cAlive, cFaulty>>

DieParticipant(pa) ==
  /\ pAlive[pa] = TRUE
  /\ pAlive' = [pAlive EXCEPT ![pa] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSent, cReqd, cRecv, cSent, cDecision, cAlive, cFaulty>>

Next ==
  \/ \E pa \in participants : SendVoteReq(pa) \/ ReceiveVote(pa) \/ DetectFault(pa)
  \/ \E pa \in participants : BroadcastDecision(pa) \/ SendVote(pa) \/ AbortOnVote(pa)
  \/ \E pa \in participants : AbortTimeoutReq(pa) \/ DecideFromBroadcast(pa)
  \/ \E pa \in participants : DieParticipant(pa) \/ DieCoordinator
  \/ MakeDecision

Spec == Init /\ [][Next]_<<pVote, pAlive, pDecision, pFaulty, pSent, cReqd, cRecv, cSent, cDecision, cAlive, cFaulty>>

\* Safety: no two participants ever decide differently, commit requires unanimity, abort
\* requires at least one no vote or a fault somewhere, and each decision is irreversible.
NoDoubleDecision ==
  /\ ~ \E pa, pb \in participants : pDecision[pa] = commit /\ pDecision[pb] = abort
  /\ (\E pa \in participants : pDecision[pa] = commit) => \A pa \in participants : pVote[pa] = yes
  /\ (\E pa \in participants : pDecision[pa] = abort) =>
       (\E pa \in participants : pVote[pa] = no) \/ (\E pa \in participants : pFaulty[pa]) \/ cFaulty
  /\ \A pa \in participants : (pDecision[pa] = commit) ~> (pDecision[pa] = commit)
  /\ \A pa \in participants : (pDecision[pa] = abort) ~> (pDecision[pa] = abort)

\* Liveness: either everyone decides or some participant/coordinator is faulty.
DecideOrFault ==
  <>(\A pa \in participants : pDecision[pa] # undecided \/ pFaulty[pa] \/ cFaulty)

====