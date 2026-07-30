---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, pAlive, pDecided, pFaulty, voted, phase,
          recvVote, sentDecision, cDecided, cAlive, cFaulty

vars == <<vote, pAlive, pDecided, pFaulty, voted, phase,
           recvVote, sentDecision, cDecided, cAlive, cFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecided \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ phase \in [participants -> {waiting, notsent}]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]
  /\ cDecided \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecided = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ phase = [p \in participants |-> waiting]
  /\ recvVote = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]
  /\ cDecided = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

ReqVote(p) ==
  /\ cAlive
  /\ phase[p] = waiting
  /\ phase' = [phase EXCEPT ![p] = notsent]
  /\ UNCHANGED <<vote, pAlive, pDecided, pFaulty,
                 voted, recvVote, sentDecision, cDecided,
                 cAlive, cFaulty>>

RecvVote(p) ==
  /\ cAlive
  /\ cDecided = undecided
  /\ phase[p] = notsent
  /\ recvVote[p] = waiting
  /\ voted[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, pAlive, pDecided, pFaulty,
                 voted, phase, sentDecision, cDecided,
                 cAlive, cFaulty>>

DetectFault(p) ==
  /\ cAlive
  /\ cDecided = undecided
  /\ phase[p] = notsent
  /\ recvVote[p] = waiting
  /\ ~pAlive[p]
  /\ cDecided' = abort
  /\ UNCHANGED <<vote, pAlive, pDecided, pFaulty,
                 voted, phase, recvVote, sentDecision,
                 cAlive, cFaulty>>

Decide ==
  /\ cAlive
  /\ cDecided = undecided
  /\ \A p \in participants : recvVote[p] \in {yes, no}
  /\ cDecided' = (IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<vote, pAlive, pDecided, pFaulty,
                 voted, phase, recvVote, sentDecision,
                 cAlive, cFaulty>>

Broadcast(p) ==
  /\ cAlive
  /\ cDecided \in {commit, abort}
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = cDecided]
  /\ UNCHANGED <<vote, pAlive, pDecided, pFaulty,
                 voted, phase, recvVote, cDecided,
                 cAlive, cFaulty>>

CoordDie ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<vote, pAlive, pDecided, pFaulty,
                 voted, phase, recvVote, sentDecision, cDecided,
                 cFaulty>>

SendVote(p) ==
  /\ pAlive[p]
  /\ phase[p] # waiting
  /\ ~voted[p]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, pAlive, pDecided, pFaulty,
                 phase, recvVote, sentDecision, cDecided,
                 cAlive, cFaulty>>

AbortOnVote(p) ==
  /\ pAlive[p]
  /\ pDecided[p] = undecided
  /\ voted[p]
  /\ vote[p] = no
  /\ pDecided' = [pDecided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, pAlive, pFaulty,
                 voted, phase, recvVote, sentDecision,
                 cDecided, cAlive, cFaulty>>

AbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pDecided[p] = undecided
  /\ ~cAlive
  /\ phase[p] = waiting
  /\ pDecided' = [pDecided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, pAlive, pFaulty,
                 voted, phase, recvVote, sentDecision,
                 cDecided, cAlive, cFaulty>>

DecideOnBroadcast(p) ==
  /\ pAlive[p]
  /\ pDecided[p] = undecided
  /\ sentDecision[p] # notsent
  /\ pDecided' = [pDecided EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, pAlive, pFaulty,
                 voted, phase, recvVote, sentDecision,
                 cDecided, cAlive, cFaulty>>

PartDie(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, pDecided,
                 voted, phase, recvVote, sentDecision,
                 cDecided, cAlive, cFaulty>>

Next ==
  \/ \E p \in participants : ReqVote(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ Decide
  \/ \E p \in participants : Broadcast(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideOnBroadcast(p)
  \/ \E p \in participants : PartDie(p)

Spec == Init /\ [][Next]_vars

AC1 == \A p1, p2 \in participants : ~(pDecided[p1] = commit /\ pDecided[p2] = abort)

AC2 == (\E p \in participants : pDecided[p] = commit)
         => (\A p \in participants : vote[p] = yes)

AC3 == (\E p \in participants : pDecided[p] = abort)
         => (\E p \in participants : vote[p] = no \/ pFaulty[p] \/ cFaulty)

AC4 == \A p \in participants :
        /\ (pDecided[p] = commit) ~> (pDecided[p] = commit)
        /\ (pDecided[p] = abort) ~> (pDecided[p] = abort)

LiveDecide ==
  <>(\A p \in participants : pDecided[p] # undecided \/ pFaulty[p] \/ cFaulty)

====