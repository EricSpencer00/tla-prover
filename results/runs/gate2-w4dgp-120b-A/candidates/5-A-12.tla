---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, psent, reqsent, rcv, broadcasted, rdecision, ralive, rfaulty

vars == <<pvote, palive, pdecision, pfaulty, psent, reqsent, rcv, broadcasted, rdecision, ralive, rfaulty>>

Init ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ psent = [p \in participants |-> FALSE]
  /\ reqsent = [p \in participants |-> FALSE]
  /\ rcv = [p \in participants |-> waiting]
  /\ broadcasted = [p \in participants |-> notsent]
  /\ rdecision = undecided
  /\ ralive = TRUE
  /\ rfaulty = FALSE

AllRequested == \A p \in participants: reqsent[p]
AllVotesReceived == \A p \in participants: rcv[p] # waiting
AllBroadcasted == \A p \in participants: broadcasted[p] # notsent
AllVotedYes == \A p \in participants: pvote[p] = yes

SendReq(p) ==
  /\ ralive
  /\ ~reqsent[p]
  /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent, rcv, broadcasted, rdecision, ralive, rfaulty>>

RecvVote(p) ==
  /\ ralive
  /\ rdecision = undecided
  /\ AllRequested
  /\ rcv[p] = waiting
  /\ psent[p]
  /\ rcv' = [rcv EXCEPT ![p] = pvote[p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent, reqsent, broadcasted, rdecision, ralive, rfaulty>>

DetectPartFailure(p) ==
  /\ ralive
  /\ rdecision = undecided
  /\ AllRequested
  /\ rcv[p] = waiting
  /\ ~palive[p]
  /\ rdecision' = abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent, reqsent, rcv, broadcasted, ralive, rfaulty>>

Decide ==
  /\ ralive
  /\ rdecision = undecided
  /\ AllRequested
  /\ AllVotesReceived
  /\ rdecision' = IF AllVotedYes THEN commit ELSE abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent, reqsent, rcv, broadcasted, ralive, rfaulty>>

Broadcast(p) ==
  /\ ralive
  /\ rdecision # undecided
  /\ broadcasted[p] = notsent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = rdecision]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent, reqsent, rcv, rdecision, ralive, rfaulty>>

CoordDie ==
  /\ ralive
  /\ ralive' = FALSE
  /\ rfaulty' = TRUE
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent, reqsent, rcv, broadcasted, rdecision, ralive, rfaulty>>

SendVote(p) ==
  /\ palive[p]
  /\ reqsent[p]
  /\ ~psent[p]
  /\ psent' = [psent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, reqsent, rcv, broadcasted, rdecision, ralive, rfaulty>>

PartAbortVote(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ psent[p]
  /\ pvote[p] = no
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, psent, reqsent, rcv, broadcasted, rdecision, ralive, rfaulty>>

PartAbortNoReq(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ ~ralive
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, psent, reqsent, rcv, broadcasted, rdecision, ralive, rfaulty>>

DecideFromBroadcast(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ broadcasted[p] # notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<pvote, palive, pfaulty, psent, reqsent, rcv, broadcasted, rdecision, ralive, rfaulty>>

PartDie(p) ==
  /\ palive[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, psent, reqsent, rcv, broadcasted, rdecision, ralive, rfaulty>>

Next ==
  \/ \E p \in participants: SendReq(p) \/ RecvVote(p) \/ DetectPartFailure(p) \/ Broadcast(p) \/ SendVote(p) \/ PartAbortVote(p) \/ PartAbortNoReq(p) \/ DecideFromBroadcast(p) \/ PartDie(p)
  \/ Decide
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: SendReq(p))
  /\ WF_vars(\E p \in participants: RecvVote(p))
  /\ WF_vars(\E p \in participants: SendVote(p))
  /\ WF_vars(\E p \in participants: PartAbortVote(p))
  /\ WF_vars(\E p \in participants: PartAbortNoReq(p))
  /\ WF_vars(\E p \in participants: DecideFromBroadcast(p))

TypeInv ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ psent \in [participants -> BOOLEAN]
  /\ reqsent \in [participants -> BOOLEAN]
  /\ rcv \in [participants -> {waiting, yes, no}]
  /\ broadcasted \in [participants -> {notsent, commit, abort}]
  /\ rdecision \in {undecided, commit, abort}
  /\ ralive \in BOOLEAN
  /\ rfaulty \in BOOLEAN

CommitAgreement ==
  \A p1, p2 \in participants: ~(pdecision[p1] = commit /\ pdecision[p2] = abort)

CommitValidity ==
  \A p \in participants: pdecision[p] = commit => AllVotedYes

AbortValidity ==
  \E p \in participants: pdecision[p] = abort
    => (\E p \in participants: pvote[p] = no \/ pfaulty[p] = TRUE \/ rfaulty = TRUE)

Irreversible ==
  \A p \in participants: (pdecision[p] = commit) ~> (pdecision[p] = commit) /\ (pdecision[p] = abort) ~> (pdecision[p] = abort)

EventualDecisionOrFailure ==
  (\A p \in participants: pdecision[p] # undecided) \/ (\E p \in participants: pfaulty[p] = TRUE) \/ (rfaulty = TRUE)

====