---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cBcast, cDecision, cAlive, cfaulty, ptable

vars == <<pvote, pAlive, pSent, cReq, cVote, cBcast, cDecision, cAlive, cfaulty, ptable>>

Predecs == {notsent, commit, abort}

TypeInv ==
  /\ pvote \in [participants -> {yes, no, undecided}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ cReq \in {waiting, yes, no, undecided}
  /\ cVote \in {yes, no, undecided}
  /\ cBcast \in [participants -> {notsent, commit, abort}]
  /\ cDecision \in {notsent, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cfaulty \in BOOLEAN
  /\ ptable \in [participants -> [participants -> Predecs]]

Init ==
  /\ pvote = [p \in participants |-> undecided]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ pSent = [p \in participants |-> FALSE]
  /\ cReq = waiting
  /\ cVote = undecided
  /\ cBcast = [p \in participants |-> notsent]
  /\ cDecision = notsent
  /\ cAlive = TRUE
  /\ cfaulty = FALSE
  /\ ptable = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ cAlive
  /\ cReq = waiting
  /\ cReq' = undecided
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cVote, cBcast, cDecision, cfaulty, ptable>>

DetectFault ==
  /\ cAlive
  /\ cReq = waiting
  /\ cAlive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cBcast, cDecision, ptable>>

GetVote(p) ==
  /\ cAlive
  /\ cReq = undecided
  /\ pAlive[p]
  /\ pvote[p] = undecided
  /\ cVote' = yes
  /\ pvote' = [pvote EXCEPT ![p] = yes]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ cReq' = yes
  /\ UNCHANGED <<pAlive, pdecision, pfaulty, cBcast, cDecision, cAlive, cfaulty, ptable>>

MakeDecision ==
  /\ cAlive
  /\ cVote = yes
  /\ cReq = yes
  /\ cDecision' = commit
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cBcast, cAlive, cfaulty, ptable>>

AbortDecision ==
  /\ cAlive
  /\ cReq = yes
  /\ cVote = no
  /\ cDecision' = abort
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cBcast, cAlive, cfaulty, ptable>>

Broadcast(p) ==
  /\ cAlive
  /\ cDecision # notsent
  /\ cBcast[p] = notsent
  /\ cBcast' = [cBcast EXCEPT ![p] = cDecision]
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cDecision, cAlive, cfaulty, ptable>>

Die ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cBcast, cDecision, ptable>>

SendVote(p) == GetVote(p)

SendAbort(p) == AbortDecision

PredecideFromCoordinator(p) ==
  /\ pAlive[p]
  /\ pdecision[p] = undecided
  /\ ptable[p][p] = notsent
  /\ cBcast[p] # notsent
  /\ ptable' = [ptable EXCEPT ![p][p] = cBcast[p]]
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cBcast, cDecision, cAlive, cfaulty>>

PredecideFromForward(p) ==
  /\ pAlive[p]
  /\ pdecision[p] = undecided
  /\ ptable[p][p] = notsent
  /\ \E q \in participants : ptable[q][p] # notsent
  /\ ptable' = [ptable EXCEPT ![p][p] = IF \E q \in participants : ptable[q][p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cBcast, cDecision, cAlive, cfaulty>>

Forward(p, q) ==
  /\ pAlive[p]
  /\ pAlive[q]
  /\ pdecision[p] = undecided
  /\ ptable[p][p] # notsent
  /\ ptable[p][q] = notsent
  /\ ptable' = [ptable EXCEPT ![p][q] = ptable[p][p]]
  /\ UNCHANGED <<pvote, pAlive, pdecision, pfaulty, pSent, cReq, cVote, cBcast, cDecision, cAlive, cfaulty>>

Decide(p) ==
  /\ pAlive[p]
  /\ pdecision[p] = undecided
  /\ ptable[p][p] # notsent
  /\ \A q \in participants : ptable[p][q] = ptable[p][p]
  /\ pdecision' = [pdecision EXCEPT ![p] = ptable[p][p]]
  /\ UNCHANGED <<pvote, pAlive, pfaulty, pSent, cReq, cVote, cBcast, cDecision, cAlive, cfaulty, ptable>>

AbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pdecision[p] = undecided
  /\ ~cAlive
  /\ \A q \in participants : cBcast[q] = notsent
  /\ (\A q \in participants : pAlive[q] => ptable[q][p] = notsent)
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, pAlive, pfaulty, pSent, cReq, cVote, cBcast, cDecision, cAlive, cfaulty, ptable>>

DieParticipant(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, pSent, cReq, cVote, cBcast, cDecision, cAlive, cfaulty, ptable>>

Next ==
  \/ SendRequest \/ DetectFault \/ MakeDecision \/ AbortDecision \/ Die \/ DieParticipant
  \/ \E p \in participants : SendVote(p) \/ SendAbort(p) \/ PredecideFromCoordinator(p)
                                \/ PredecideFromForward(p) \/ Decide(p) \/ AbortOnTimeout(p)
  \/ \E p \in participants, q \in participants : Broadcast(p) \/ Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendVote('m1'))
  /\ WF_vars(SendVote('m2'))
  /\ WF_vars(SendAbort('m1'))
  /\ WF_vars(SendAbort('m2'))
  /\ WF_vars(PredecideFromCoordinator('m1'))
  /\ WF_vars(PredecideFromCoordinator('m2'))
  /\ WF_vars(PredecideFromForward('m1'))
  /\ WF_vars(PredecideFromForward('m2'))
  /\ WF_vars(Decide('m1'))
  /\ WF_vars(Decide('m2'))
  /\ WF_vars(AbortOnTimeout('m1'))
  /\ WF_vars(AbortOnTimeout('m2'))

AC1 == \A p \in participants : pdecision[p] = commit => \A q \in participants : pdecision[q] = commit
AC2 == (\E p \in participants : pdecision[p] = commit) => (\A q \in participants : pvote[q] = yes)
AC3 == (\E p \in participants : pdecision[p] = abort) => (\E q \in participants : pvote[q] = no \/ pfaulty[q] \/ cfaulty)
AC4 == \A p \in participants : \A d \in {commit, abort} : (pdecision[p] = d) ~> (pdecision[p] = d)

AC3Liveness == <>(\A p \in participants : pdecision[p] # undecided \/ \E p \in participants : pfaulty[p] \/ cfaulty)
Termination == \A p \in participants : (pdecision[p] # undecided) ~> TRUE

TypeInvNB == TypeInv

====