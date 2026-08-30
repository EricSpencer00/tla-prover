---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, coordReqs, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, coordReqs, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ coordReqs \in [participants -> BOOLEAN]
  /\ coordRecv \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ \E v \in {yes, no} : \A p \in participants : pVote[p] = v
  /\ \A p \in participants : pAlive[p] = TRUE
  /\ \A p \in participants : pDecision[p] = undecided
  /\ \A p \in participants : pFaulty[p] = FALSE
  /\ \A p \in participants : pSent[p] = FALSE
  /\ coordReqs = [p \in participants |-> FALSE]
  /\ coordRecv = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendReq(p) ==
  /\ coordAlive
  /\ ~coordReqs[p]
  /\ coordReqs' = [coordReqs EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReqs[p]
  /\ coordRecv[p] = waiting
  /\ pSent[p]
  /\ coordRecv' = [coordRecv EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReqs, coordSent, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReqs[p]
  /\ coordRecv[p] = waiting
  /\ ~pAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReqs, coordRecv, coordSent, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordReqs[p]
  /\ \A p \in participants : coordRecv[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReqs, coordRecv, coordSent, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReqs, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReqs, coordRecv, coordSent, coordDecision, coordFaulty>>

SendVote(p) ==
  /\ pAlive[p]
  /\ coordReqs[p]
  /\ ~pSent[p]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, coordReqs, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnNo(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ pSent[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReqs, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ ~coordAlive
  /\ ~coordReqs[p]
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReqs, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideFromCoord(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ coordSent[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReqs, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSent, coordReqs, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendReq(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : Broadcast(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnNo(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromCoord(p)
  \/ \E p \in participants : PartDie(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendReq(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnNo(p))
  /\ WF_vars(\E p \in participants : DecideFromCoord(p))
  /\ WF_vars(MakeDecision)

NoConflictingDecisions ==
  \A p, q \in participants :
    (pDecision[p] = commit /\ pDecision[q] = abort) => p = q

CommitOnlyOnUnanimousYes ==
  \A p \in participants : pDecision[p] = commit => (\A q \in participants : pVote[q] = yes)

AbortOnlyOnNoOrFault ==
  \A p \in participants :
    pDecision[p] = abort =>
      \/ \E q \in participants : pVote[q] = no
      \/ \E q \in participants : pFaulty[q]
      \/ coordFaulty

Irreversible == \A p \in participants : (pDecision[p] = commit) ~> (pDecision[p] = commit)

EventuallyDecide == <>(\A p \in participants : pDecision[p] # undecided \/ coordFaulty \/ (\E q \in participants : pFaulty[q]))

Properties == NoConflictingDecisions /\ CommitOnlyOnUnanimousYes /\ AbortOnlyOnNoOrFault /\ Irreversible /\ EventuallyDecide

====