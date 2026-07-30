---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES plVote, plAlive, plDecision, plFaulty, plSentVote, coordReqd, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == <<plVote, plAlive, plDecision, plFaulty, plSentVote, coordReqd, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ plVote \in [participants -> {yes, no}]
  /\ plAlive \in [participants -> BOOLEAN]
  /\ plDecision \in [participants -> {undecided, commit, abort}]
  /\ plFaulty \in [participants -> BOOLEAN]
  /\ plSentVote \in [participants -> BOOLEAN]
  /\ coordReqd \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ plVote \in [participants -> {yes, no}]
  /\ plAlive = [p \in participants |-> TRUE]
  /\ plDecision = [p \in participants |-> undecided]
  /\ plFaulty = [p \in participants |-> FALSE]
  /\ plSentVote = [p \in participants |-> FALSE]
  /\ coordReqd = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendVoteReq(p) ==
  /\ coordAlive
  /\ ~coordReqd[p]
  /\ coordReqd' = [coordReqd EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<plVote, plAlive, plDecision, plFaulty, plSentVote, coordVote, coordBroadcast, coordDecision, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReqd[p]
  /\ coordVote[p] = waiting
  /\ plAlive[p]
  /\ plSentVote[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = plVote[p]]
  /\ UNCHANGED <<plVote, plAlive, plDecision, plFaulty, plSentVote, coordReqd, coordBroadcast, coordDecision, coordFaulty>>

DetectPartFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReqd[p]
  /\ coordVote[p] = waiting
  /\ ~plAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<plVote, plAlive, plDecision, plFaulty, plSentVote, coordReqd, coordVote, coordBroadcast, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordReqd[p]
  /\ \A p \in participants : coordVote[p] \in {yes, no}
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<plVote, plAlive, plDecision, plFaulty, plSentVote, coordReqd, coordVote, coordBroadcast, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = notsent
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<plVote, plAlive, plDecision, plFaulty, plSentVote, coordReqd, coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<plVote, plAlive, plDecision, plFaulty, plSentVote, coordReqd, coordVote, coordBroadcast, coordDecision>>

SendVote(p) ==
  /\ plAlive[p]
  /\ coordReqd[p]
  /\ ~plSentVote[p]
  /\ plSentVote' = [plSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<plVote, plAlive, plDecision, plFaulty, coordReqd, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ plAlive[p]
  /\ plDecision[p] = undecided
  /\ plSentVote[p]
  /\ plVote[p] = no
  /\ plDecision' = [plDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<plVote, plAlive, plFaulty, plSentVote, coordReqd, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ plAlive[p]
  /\ plDecision[p] = undecided
  /\ ~coordAlive
  /\ ~coordReqd[p]
  /\ plDecision' = [plDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<plVote, plAlive, plFaulty, plSentVote, coordReqd, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ plAlive[p]
  /\ plDecision[p] = undecided
  /\ coordBroadcast[p] # notsent
  /\ plDecision' = [plDecision EXCEPT ![p] = coordBroadcast[p]]
  /\ UNCHANGED <<plVote, plAlive, plFaulty, plSentVote, coordReqd, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ plAlive[p]
  /\ plAlive' = [plAlive EXCEPT ![p] = FALSE]
  /\ plFaulty' = [plFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<plVote, plDecision, plSentVote, coordReqd, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendVoteReq(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectPartFault(p)
  \/ MakeDecision
  \/ \E p \in participants : Broadcast(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideOnBroadcast(p)
  \/ \E p \in participants : PartDie(p)

Spec == Init /\ [][Next]_vars
  /\ SF_vars(\E p \in participants : SendVoteReq(p))
  /\ WF_vars(\E p \in participants : RecvVote(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : Deciding(p))

Deciding(p) ==
  \/ \E q \in participants : Broadcast(q)
  \/ AbstOnVote(p)
  \/ DecidingOnBroadcast(p)

AbstOnVote(p) == AbortOnVote(p)
DecidingOnBroadcast(p) == DecideOnBroadcast(p)

AC1 == \A p1 \in participants : \A p2 \in participants : ~(plDecision[p1] = commit /\ plDecision[p2] = abort)

AC2 == \A p \in participants : plDecision[p] = commit => (\A q \in participants : plVote[q] = yes)

AC3 == \A p \in participants : plDecision[p] = abort => (\E q \in participants : plVote[q] = no \/ plFaulty[q] \/ coordFaulty)

AC4 == \A p \in participants : (plDecision[p] = commit) ~> (plDecision[p] = commit) /\ (plDecision[p] = abort) ~> (plDecision[p] = abort)

AC3Liveness == <>(\A p \in participants : plDecision[p] # undecided) \/ (\E p \in participants : plFaulty[p]) \/ coordFaulty

====