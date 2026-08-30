---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfault, prequested, pvoteRecvd,
          pdecisionSent, cdecision, calive, cfault

vars == <<pvote, palive, pdecision, pfault, prequested, pvoteRecvd,
           pdecisionSent, cdecision, calive, cfault>>

TypeInv ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pfault \in [participants -> BOOLEAN]
  /\ prequested \in [participants -> BOOLEAN]
  /\ pvoteRecvd \in [participants -> {yes, no, waiting}]
  /\ pdecisionSent \in [participants -> {committed, notsent}]
  /\ cdecision \in {undecided, commit, abort}
  /\ calive \in BOOLEAN
  /\ cfault \in BOOLEAN

Init ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfault = [p \in participants |-> FALSE]
  /\ prequested = [p \in participants |-> FALSE]
  /\ pvoteRecvd = [p \in participants |-> waiting]
  /\ pdecisionSent = [p \in participants |-> notsent]
  /\ cdecision = undecided
  /\ calive = TRUE
  /\ cfault = FALSE

SendVoteReq(p) ==
  /\ calive
  /\ ~prequested[p]
  /\ prequested' = [prequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfault, pvoteRecvd,
                 pdecisionSent, cdecision, calive, cfault>>

ReceiveVote(p) ==
  /\ calive
  /\ cdecision = undecided
  /\ prequested[p]
  /\ pvoteRecvd[p] = waiting
  /\ palive[p]
  /\ pvoteRecvd' = [pvoteRecvd EXCEPT ![p] = pvote[p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfault, prequested,
                 pdecisionSent, cdecision, calive, cfault>>

DetectFault(p) ==
  /\ calive
  /\ cdecision = undecided
  /\ prequested[p]
  /\ pvoteRecvd[p] = waiting
  /\ ~palive[p]
  /\ cdecision' = abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfault, prequested,
                 pvoteRecvd, pdecisionSent, calive, cfault>>

MakeDecision ==
  /\ calive
  /\ cdecision = undecided
  /\ \A p \in participants : prequested[p]
  /\ \A p \in participants : pvoteRecvd[p] # waiting
  /\ cdecision' = IF \A p \in participants : pvote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfault, prequested,
                 pvoteRecvd, pdecisionSent, calive, cfault>>

BroadcastDecision(p) ==
  /\ calive
  /\ cdecision # undecided
  /\ pdecisionSent[p] = notsent
  /\ pdecisionSent' = [pdecisionSent EXCEPT ![p] = cdecision]
  /\ UNCHANGED <<pvote, palive, pdecision, pfault, prequested,
                 pvoteRecvd, cdecision, calive, cfault>>

CoordinatorDie ==
  /\ calive
  /\ calive' = FALSE
  /\ cfault' = TRUE
  /\ UNCHANGED <<pvote, palive, pdecision, pfault, prequested,
                 pvoteRecvd, pdecisionSent, cdecision>>

SendVote(p) ==
  /\ palive[p]
  /\ prequested[p]
  /\ pvoteRecvd[p] = waiting
  /\ pvoteRecvd' = [pvoteRecvd EXCEPT ![p] = pvote[p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfault, prequested,
                 pdecisionSent, cdecision, calive, cfault>>

AbortOnVote(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ pvote[p] = no
  /\ pvoteRecvd[p] = pvote[p]
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfault, prequested, pvoteRecvd,
                 pdecisionSent, cdecision, calive, cfault>>

AbortOnTimeoutReq(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ ~prequested[p]
  /\ cfault
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfault, prequested, pvoteRecvd,
                 pdecisionSent, cdecision, calive, cfault>>

DecideFromCoordinator(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ pdecisionSent[p] # notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = pdecisionSent[p]]
  /\ UNCHANGED <<pvote, palive, pfault, prequested, pvoteRecvd,
                 pdecisionSent, cdecision, calive, cfault>>

ParticipantDie(p) ==
  /\ palive[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ pfault' = [pfault EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, prequested, pvoteRecvd,
                 pdecisionSent, cdecision, calive, cfault>>

Next ==
  \/ \E p \in participants: SendVoteReq(p) \/ ReceiveVote(p) \/ DetectFault(p)
                               \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
                               \/ AbortOnTimeoutReq(p) \/ DecideFromCoordinator(p)
                               \/ ParticipantDie(p)
  \/ MakeDecision
  \/ CoordinatorDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants: WF_vars(SendVoteReq(p)) /\ WF_vars(ReceiveVote(p))
  /\ WF_vars(MakeDecision)
  /\ \A p \in participants: WF_vars(SendVote(p)) /\ WF_vars(DecideFromCoordinator(p))
  /\ \A p \in participants: SF_vars(AbortOnVote(p)) /\ SF_vars(AbortOnTimeoutReq(p))

NoTwoDecideDifferently ==
  \A p, q \in participants : (pdecision[p] = commit /\ pdecision[q] = abort) => FALSE

CommitOnlyIfAllYes ==
  (\E p \in participants : pdecision[p] = commit) => (\A p \in participants : pvote[p] = yes)

AbortOnlyIfNoVoteOrFault ==
  (\E p \in participants : pdecision[p] = abort)
    => (\E p \in participants : pvote[p] = no) \/ (\E p \in participants : pfault[p]) \/ cfault

DecideAtMostOnce ==
  \A p \in participants :
    /\ (pdecision[p] = commit => (\A q \in participants : pdecision[q] = commit \/ pdecision[q] = undecided))
    /\ (pdecision[p] = abort => (\A q \in participants : pdecision[q] = abort \/ pdecision[q] = undecided))

AllDecideOrSomeoneFault ==
  <>(\A p \in participants : pdecision[p] # undecided) \/ (\E p \in participants : pfault[p]) \/ cfault

====