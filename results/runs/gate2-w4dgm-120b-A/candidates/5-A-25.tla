---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, pAlive, pDecision, pFaulty, pSent, coordSent, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == <<pvote, pAlive, pDecision, pFaulty, pSent, coordSent, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
    /\ pvote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ coordSent \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {waiting, yes, no}]
    /\ coordBroadcast \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pvote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ coordSent = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SentAll == \A p \in participants : pSent[p]
RecvAll == \A p \in participants : coordRecv[p] # waiting
AllYes == \A p \in participants : pvote[p] = yes
SomeNo == \E p \in participants : pvote[p] = no

CoordinatorActs ==
    \/ (\E p \in participants :
          /\ coordAlive
          /\ ~coordSent[p]
          /\ coordSent' = [coordSent EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<pvote, pAlive, pDecision, pFaulty, pSent, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>)
    \/ (\E p \in participants :
          /\ coordAlive
          /\ coordDecision = undecided
          /\ coordSent[p]
          /\ coordRecv[p] = waiting
          /\ pSent[p]
          /\ coordRecv' = [coordRecv EXCEPT ![p] = pvote[p]]
          /\ UNCHANGED <<pvote, pAlive, pDecision, pFaulty, pSent, coordSent, coordBroadcast, coordDecision, coordAlive, coordFaulty>>)
    \/ (\E p \in participants :
          /\ coordAlive
          /\ coordDecision = undecided
          /\ coordSent[p]
          /\ coordRecv[p] = waiting
          /\ ~pAlive[p]
          /\ ~pSent[p]
          /\ coordDecision' = abort
          /\ UNCHANGED <<pvote, pAlive, pDecision, pFaulty, pSent, coordSent, coordRecv, coordBroadcast, coordAlive, coordFaulty>>)
    \/ (\E p \in participants :
          /\ coordAlive
          /\ coordDecision = undecided
          /\ coordRecv[p] # waiting
          /\ RecvAll
          /\ coordDecision' = (IF AllYes THEN commit ELSE abort)
          /\ UNCHANGED <<pvote, pAlive, pDecision, pFaulty, pSent, coordSent, coordRecv, coordBroadcast, coordAlive, coordFaulty>>)
    \/ (\E p \in participants :
          /\ coordAlive
          /\ coordDecision # undecided
          /\ coordBroadcast[p] = notsent
          /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
          \/ UNCHANGED <<pvote, pAlive, pDecision, pFaulty, pSent, coordSent, coordRecv, coordDecision, coordAlive, coordFaulty>>)
    \/ (coordAlive /\ coordAlive' = FALSE /\ coordFaulty' = TRUE
          /\ UNCHANGED <<pvote, pAlive, pDecision, pFaulty, pSent, coordSent, coordRecv, coordBroadcast, coordDecision, coordFaulty>>)

ParticipantActs ==
    \/ (\E p \in participants :
          /\ pAlive[p]
          /\ ~pSent[p]
          /\ coordSent[p]
          /\ pSent' = [pSent EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<pvote, pAlive, pDecision, pFaulty, coordSent, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>)
    \/ (\E p \in participants :
          /\ pAlive[p]
          /\ pDecision[p] = undecided
          /\ pSent[p]
          /\ pvote[p] = no
          /\ pDecision' = [pDecision EXCEPT ![p] = abort]
          /\ UNCHANGED <<pvote, pAlive, pSent, pFaulty, coordSent, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>)
    \/ (\E p \in participants :
          /\ pAlive[p]
          /\ pDecision[p] = undecided
          /\ ~coordAlive[p]
          /\ pDecision' = [pDecision EXCEPT ![p] = abort]
          /\ UNCHANGED <<pvote, pAlive, pSent, pFaulty, coordSent, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>)
    \/ (\E p \in participants :
          /\ pAlive[p]
          /\ pDecision[p] = undecided
          /\ coordBroadcast[p] # notsent
          /\ coordBroadcast[p] # undecided
          /\ pDecision' = [pDecision EXCEPT ![p] = coordBroadcast[p]]
          /\ UNCHANGED <<pvote, pAlive, pSent, pFaulty, coordSent, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>)
    \/ (\E p \in participants :
          /\ pAlive[p]
          /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
          /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<pvote, pDecision, pSent, coordSent, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>)

Next == CoordinatorActs \/ ParticipantActs

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ParticipantActs)
    /\ WF_vars(CoordinatorActs)

AC1 == \A p, q \in participants : (pDecision[p] = commit) => (pDecision[q] # abort)
AC2 == (\E p \in participants : pDecision[p] = commit) => (\A p \in participants : pvote[p] = yes)
AC3 == (\E p \in participants : pDecision[p] = abort) => (SomeNo \/ (\E p \in participants : pFaulty[p]) \/ coordFaulty)
AC4 ==
    /\ (\A p \in participants : pDecision[p] = commit => [][pDecision[p] = commit]_vars)
    /\ (\A p \in participants : pDecision[p] = abort => [][pDecision[p] = abort]_vars)

Liveness ==
    <>(\A p \in participants : pDecision[p] # undecided \/ (\E p \in participants : pFaulty[p]) \/ coordFaulty)

StateConstraints == TypeInv

====