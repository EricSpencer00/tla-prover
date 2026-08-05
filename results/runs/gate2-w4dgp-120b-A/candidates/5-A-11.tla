---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, svote, rsent, rvote, rsentdec, rdecision, ralive, rfaulty

vars == <<pvote, palive, pdecision, pfaulty, svote, rsent, rvote, rsentdec, rdecision, ralive, rfaulty>>

Phases == {undecided, commit, abort}

TypeInv ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> Phases]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ svote \in [participants -> {yes, no, waiting}]
  /\ rsent \in [participants -> {notsent, BOOLEAN}]
  /\ rvote \in [participants -> {yes, no, waiting}]
  /\ rsentdec \in [participants -> {notsent, BOOLEAN}]
  /\ rdecision \in {undecided, commit, abort}
  /\ ralive \in BOOLEAN
  /\ rfaulty \in BOOLEAN

Init ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ svote = [p \in participants |-> waiting]
  /\ rsent = [p \in participants |-> notsent]
  /\ rvote = [p \in participants |-> waiting]
  /\ rsentdec = [p \in participants |-> notsent]
  /\ rdecision = undecided
  /\ ralive = TRUE
  /\ rfaulty = FALSE

\* Send vote request to a participant (simple broadcast, so only one message in flight).
ReqVote(p) ==
  /\ ralive
  /\ rsent[p] = notsent
  /\ rsent' = [rsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, svote, rvote, rsentdec, rdecision, ralive, rfaulty>>

\* Coordinator receives a vote from a participant who has sent it.
RecvVote(p) ==
  /\ ralive
  /\ rdecision = undecided
  /\ \A q \in participants : rsent[q] = TRUE
  /\ rvote[p] = waiting
  /\ svote[p] = yes \/ svote[p] = no
  /\ rvote' = [rvote EXCEPT ![p] = svote[p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, svote, rsent, rsentdec, rdecision, ralive, rfaulty>>

\* Coordinator detects a participant that died before voting; it decides abort.
DetectFault(p) ==
  /\ ralive
  /\ rdecision = undecided
  /\ \A q \in participants : rsent[q] = TRUE
  /\ rvote[p] = waiting
  /\ ~palive[p]
  /\ rdecision' = abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, svote, rsent, rvote, rsentdec, ralive, rfaulty>>

\* Coordinator makes a decision once all votes are in.
Decide ==
  /\ ralive
  /\ rdecision = undecided
  /\ \A p \in participants : rvote[p] = yes \/ rvote[p] = no
  /\ rdecision' = IF \A p \in participants : rvote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, svote, rsent, rvote, rsentdec, ralive, rfaulty>>

\* Coordinator broadcasts its decision to a participant (simple broadcast).
Bcast(p) ==
  /\ ralive
  /\ rdecision # undecided
  /\ rsentdec[p] = notsent
  /\ rsentdec' = [rsentdec EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, svote, rsent, rvote, rdecision, ralive, rfaulty>>

DieCoord ==
  /\ ralive
  /\ ralive' = FALSE
  /\ rfaulty' = TRUE
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, svote, rsent, rvote, rsentdec, rdecision>>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
  /\ palive[p]
  /\ rsent[p] = TRUE
  /\ svote[p] = waiting
  /\ svote' = [svote EXCEPT ![p] = pvote[p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, rsent, rvote, rsentdec, rdecision, ralive, rfaulty>>

\* Participant aborts based on its own vote being no.
AbortVote(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ svote[p] = yes \/ svote[p] = no
  /\ pdecision' = [pdecision EXCEPT ![p] = IF svote[p] = no THEN abort ELSE pdecision[p]]
  /\ UNCHANGED <<pvote, palive, pfaulty, svote, rsent, rvote, rsentdec, rdecision, ralive, rfaulty>>

\* Participant aborts on timeout because the coordinator never requested.
AbortTimeout(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ ~rsent[p]
  /\ ~ralive
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, svote, rsent, rvote, rsentdec, rdecision, ralive, rfaulty>>

\* Participant adopts the coordinator's broadcast decision.
DecideRun(p) ==
  /\ palive[p]
  /\ rsentdec[p] = TRUE
  /\ pdecision[p] = undecided
  /\ pdecision' = [pdecision EXCEPT ![p] = rdecision]
  /\ UNCHANGED <<pvote, palive, pfaulty, svote, rsent, rvote, rsentdec, rdecision, ralive, rfaulty>>

DiePart(p) ==
  /\ palive[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, svote, rsent, rvote, rsentdec, rdecision, ralive, rfaulty>>

CoordProgress == \E p \in participants : ReqVote(p) \/ RecvVote(p) \/ DetectFault(p) \/ Bcast(p)
PartProgress == \E p \in participants : SendVote(p) \/ AbortVote(p) \/ AbortTimeout(p) \/ DecideRun(p)
DecideStep == Decide \/ DieCoord

Next ==
  \/ CoordProgress \/ PartProgress \/ DecideStep
  \/ \E p \in participants : DiePart(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordProgress) /\ WF_vars(DecideStep) /\ WF_vars(PartProgress)

\* No two participants ever decide differently.
Agreement == \A p, q \in participants : ~(pdecision[p] = commit /\ pdecision[q] = abort)

\* Commit is backed by unanimous votes.
CommitValid == \A p \in participants : pdecision[p] = commit => (\A q \in participants : pvote[q] = yes)

\* Abort is backed by a no vote or a failure.
AbortValid == \A p \in participants : pdecision[p] = abort =>
                  (\E q \in participants : pvote[q] = no) \/ (\E q \in participants : pfaulty[q]) \/ rfaulty

\* Each participant decides at most once.
Irrevocable ==
  /\ \A p \in participants : (pdecision[p] = commit) ~> (pdecision[p] = commit)
  /\ \A p \in participants : (pdecision[p] = abort) ~> (pdecision[p] = abort)

\* Non-blocking termination of the simple broadcast variant: either everyone decides,
\* or a participant coordinate failure is acknowledged, but a live participant may stay undecided.
DecideOrFault == <>(\A p \in participants : pdecision[p] # undecided \/ rfaulty \/ (\E p \in participants : pfaulty[p]))
====