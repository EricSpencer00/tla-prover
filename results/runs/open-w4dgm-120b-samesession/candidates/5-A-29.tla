---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, psentVoteReq,
          csentVoteReq, cvote, cbroadcast, cdecision, calive, cfaulty

vars == <<pvote, palive, pdecision, pfaulty, psentVoteReq,
           csentVoteReq, cvote, cbroadcast, cdecision, calive, cfaulty>>

TypeInv ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ psentVoteReq \in [participants -> BOOLEAN]
  /\ csentVoteReq \in [participants -> BOOLEAN]
  /\ cvote \in [participants -> {yes, no, waiting}]
  /\ cbroadcast \in [participants -> {commit, abort, notsent}]
  /\ cdecision \in {undecided, commit, abort}
  /\ calive \in BOOLEAN
  /\ cfaulty \in BOOLEAN

Init ==
  /\ \E f \in [participants -> {yes, no}]:
       pvote = f
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ psentVoteReq = [p \in participants |-> FALSE]
  /\ csentVoteReq = [p \in participants |-> FALSE]
  /\ cvote = [p \in participants |-> waiting]
  /\ cbroadcast = [p \in participants |-> notsent]
  /\ cdecision = undecided
  /\ calive = TRUE
  /\ cfaulty = FALSE

SendVoteReq(p) ==
  /\ calive
  /\ ~csentVoteReq[p]
  /\ csentVoteReq' = [csentVoteReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVoteReq,
                 cvote, cbroadcast, cdecision, calive, cfaulty>>

RecvVote(p) ==
  /\ calive
  /\ cdecision = undecided
  /\ \A q \in participants: csentVoteReq[q]
  /\ cvote[p] = waiting
  /\ psentVoteReq[p]
  /\ cvote' = [cvote EXCEPT ![p] = pvote[p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVoteReq,
                 csentVoteReq, cbroadcast, cdecision, calive, cfaulty>>

DetectFault(p) ==
  /\ calive
  /\ cdecision = undecided
  /\ \A q \in participants: csentVoteReq[q]
  /\ cvote[p] = waiting
  /\ ~palive[p]
  /\ ~psentVoteReq[p]
  /\ cdecision' = abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVoteReq,
                 csentVoteReq, cvote, cbroadcast, calive, cfaulty>>

MakeDecision ==
  /\ calive
  /\ cdecision = undecided
  /\ \A p \in participants: cvote[p] # waiting
  /\ cdecision' = IF \A p \in participants: cvote[p] = yes
                  THEN commit ELSE abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVoteReq,
                 csentVoteReq, cvote, cbroadcast, calive, cfaulty>>

BroadcastDecision(p) ==
  /\ calive
  /\ cdecision # undecided
  /\ cbroadcast[p] = notsent
  /\ cbroadcast' = [cbroadcast EXCEPT ![p] = cdecision]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVoteReq,
                 csentVoteReq, cvote, cdecision, calive, cfaulty>>

CoordinatorDie ==
  /\ calive
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVoteReq,
                 csentVoteReq, cvote, cbroadcast, cdecision>>

SendVote(p) ==
  /\ palive[p]
  /\ csentVoteReq[p]
  /\ ~psentVoteReq[p]
  /\ psentVoteReq' = [psentVoteReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                 csentVoteReq, cvote, cbroadcast, cdecision, calive, cfaulty>>

AbortOnVote(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ psentVoteReq[p]
  /\ pvote[p] = no
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, psentVoteReq,
                 csentVoteReq, cvote, cbroadcast, cdecision, calive, cfaulty>>

AbortOnTimeout(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ ~csentVoteReq[p]
  /\ cfaulty
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, psentVoteReq,
                 csentVoteReq, cvote, cbroadcast, cdecision, calive, cfaulty>>

DecideOnBroadcast(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ cbroadcast[p] # notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = cbroadcast[p]]
  /\ UNCHANGED <<pvote, palive, pfaulty, psentVoteReq,
                 csentVoteReq, cvote, cbroadcast, cdecision, calive, cfaulty>>

ParticipantDie(p) ==
  /\ palive[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, psentVoteReq,
                 csentVoteReq, cvote, cbroadcast, cdecision, calive, cfaulty>>

Next ==
  \/ \E p \in participants:
       SendVoteReq(p) \/ RecvVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
         \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p)
         \/ ParticipantDie(p)
  \/ MakeDecision
  \/ CoordinatorDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants: SF_vars(SendVoteReq(p))
  /\ \A p \in participants: SF_vars(RecvVote(p))
  /\ \A p \in participants: WF_vars(SendVote(p))
  /\ \A p \in participants: WF_vars(DecideOnBroadcast(p))

Agreement ==
  \A p, q \in participants:
    (pdecision[p] = commit /\ pdecision[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants: (pdecision[p] = commit) => (\A q \in participants: pvote[q] = yes)

AbortValidity ==
  \A p \in participants:
    (pdecision[p] = abort) => (\E q \in participants: pvote[q] = no \/ pfaulty[q] \/ cfaulty)

Irrevocability ==
  \A p \in participants:
    /\ (pdecision[p] = commit => [pdecision EXCEPT ![p] = commit] = pdecision)
    /\ (pdecision[p] = abort => [pdecision EXCEPT ![p] = abort] = pdecision)

EventualDecisionOrCrash ==
  (\E p \in participants: pdecision[p] # undecided) \/ (\E p \in participants: pfaulty[p]) \/ cfaulty

====