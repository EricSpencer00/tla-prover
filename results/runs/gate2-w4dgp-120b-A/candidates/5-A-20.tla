---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, pAlive, pdecision, pfaulty, psent, recved, coordDecision, coordAlive, coordDecide, broadcast

vars == <<pvote, pAlive, pdecision, pfaulty, psent, recved, coordDecision, coordAlive, coordDecide, broadcast>>

NoVoters == [p \in participants |-> waiting]
NoBroadcast == [p \in participants |-> notsent]

TypeInv ==
  /\ pvote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ psent \in [participants -> BOOLEAN]
  /\ recved \in [participants -> {yes, no, waiting}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordDecide \in [participants -> {commit, abort, notsent}]
  /\ coordDecide' = coordDecide

Init ==
  /\ pvote \in [participants -> {yes, no}]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ psent = [p \in participants |-> FALSE]
  /\ recved = NoVoters
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordDecide = NoBroadcast

RequestVote(p) ==
  /\ coordAlive
  /\ recved[p] = waiting
  /\ coordDecide[p] = notsent
  /\ coordDecide' = [coordDecide EXCEPT ![p] = notsent]
  /\ TRUE

RecvedAll == \A p \in participants : recved[p] # waiting

SendReq == \E p \in participants : RequestVote(p)

CoordReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ RecvedAll
  /\ recved[p] = waiting
  /\ psent[p]
  /\ recved' = [recved EXCEPT ![p] = pvote[p]]
  /\ TRUE

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ RecvedAll
  /\ recved[p] = waiting
  /\ ~pAlive[p]
  /\ coordDecision' = abort
  /\ TRUE

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ RecvedAll
  /\ coordDecision' = IF \A p \in participants : recved[p] = yes THEN commit ELSE abort
  /\ TRUE

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordDecide[p] = notsent
  /\ coordDecide' = [coordDecide EXCEPT ![p] = coordDecision]
  /\ TRUE

SendBroadcast == \E p \in participants : BroadcastDecision(p)

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordDecide' = [p \in participants |-> coordDecision]
  /\ TRUE

SendVote(p) ==
  /\ pAlive[p]
  /\ coordDecide[p] # notsent
  /\ ~psent[p]
  /\ psent' = [psent EXCEPT ![p] = TRUE]
  /\ TRUE

DecisionAbort(p) ==
  /\ pAlive[p]
  /\ pdecision[p] = undecided
  /\ (coordDecide[p] # notsent \/ pvote[p] = no)
  /\ pdecision' = [pdecision EXCEPT ![p] = IF coordDecide[p] # notsent THEN coordDecide[p] ELSE abort]
  /\ TRUE

VoteDecision == \E p \in participants : SendVote(p)

Decide == \E p \in participants : DecisionAbort(p)

ParticipantTimeout(p) ==
  /\ pAlive[p]
  /\ pdecision[p] = undecided
  /\ ~coordAlive
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ TRUE

ParticipantTimeoutAny == \E p \in participants : ParticipantTimeout(p)

ParticipantDie(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ TRUE

ParticipantCrash == \E p \in participants : ParticipantDie(p)

Next ==
  \/ SendReq
  \/ VoteDecision
  \/ Decide
  \/ SendBroadcast
  \/ ParticipantTimeoutAny
  \/ ParticipantCrash
  \/ \E p \in participants : CoordReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ CoordDie

Spec == Init /\ [][Next]_vars
  /\ WF_vars(VoteDecision)
  /\ WF_vars(Decide)
  /\ WF_vars(SendBroadcast)
  /\ WF_vars(ParticipantTimeoutAny)

Agreement ==
  \A p, q \in participants :
    (pdecision[p] = commit /\ pdecision[q] = abort) => p = q

CommitValid == \A p \in participants : pdecision[p] = commit => \A q \in participants : pvote[q] = yes

AbortValid ==
  \A p \in participants : pdecision[p] = abort =>
    (\E q \in participants : pvote[q] = no) \/ (\E q \in participants : pfaulty[q]) \/ ~coordAlive

Irrevocable ==
  \A p \in participants : (pdecision[p] = commit => pdecision' = [pdecision EXCEPT ![p] = commit])
    /\ (pdecision[p] = abort => pdecision' = [pdecision EXCEPT ![p] = abort])

DecisionProgress ==
  <>(\A p \in participants : pdecision[p] # undecided \/ \E q \in participants : pfaulty[q] \/ ~coordAlive)

====