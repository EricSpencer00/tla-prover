---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

States == {undecided, commit, abort}

VARIABLES pvote, palive, pfinal, pfaulty, psentreq
           coordReqs, coordRecv, coordBroadcast, coordDecide, coordAlive, coordFaulty

vars == <<pvote, palive, pfinal, pfaulty, psentreq,
          coordReqs, coordRecv, coordBroadcast, coordDecide, coordAlive, coordFaulty>>

TypeOK ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pfinal \in [participants -> States]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ psentreq \in [participants -> BOOLEAN]
    /\ coordReqs \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
    /\ coordDecide \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive = [p \in participants |-> TRUE]
    /\ pfinal = [p \in participants |-> undecided]
    /\ pfaulty = [p \in participants |-> FALSE]
    /\ psentreq = [p \in participants |-> FALSE]
    /\ coordReqs = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecide = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

CoordSendReq(p) ==
    /\ coordAlive
    /\ ~coordReqs[p]
    /\ coordReqs' = [coordReqs EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pfinal, pfaulty, psentreq,
                   coordRecv, coordBroadcast, coordDecide, coordAlive, coordFaulty>>

CoordReceive(p) ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ \A q \in participants : coordReqs[q]
    /\ coordRecv[p] = waiting
    /\ psentreq[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED <<pvote, palive, pfinal, pfaulty, psentreq,
                   coordReqs, coordBroadcast, coordDecide, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ \A q \in participants : coordReqs[q]
    /\ coordRecv[p] = waiting
    /\ ~psentreq[p]
    /\ ~palive[p]
    /\ coordDecide' = abort
    /\ UNCHANGED <<pvote, palive, pfinal, pfaulty, psentreq,
                   coordReqs, coordRecv, coordBroadcast, coordAlive, coordFaulty>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ \A p \in participants : coordRecv[p] # waiting
    /\ coordDecide' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pvote, palive, pfinal, pfaulty, psentreq,
                   coordReqs, coordRecv, coordBroadcast, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecide # undecided
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecide]
    /\ UNCHANGED <<pvote, palive, pfinal, pfaulty, psentreq,
                   coordReqs, coordRecv, coordDecide, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pvote, palive, pfinal, pfaulty, psentreq,
                   coordReqs, coordRecv, coordBroadcast, coordDecide, coordFaulty>>

PartSendVote(p) ==
    /\ palive[p]
    /\ coordReqs[p]
    /\ ~psentreq[p]
    /\ psentreq' = [psentreq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pfinal, pfaulty,
                   coordReqs, coordRecv, coordBroadcast, coordDecide, coordAlive, coordFaulty>>

PartAbortOnVote(p) ==
    /\ palive[p]
    /\ pfinal[p] = undecided
    /\ psentreq[p]
    /\ pvote[p] = no
    /\ pfinal' = [pfinal EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psentreq,
                   coordReqs, coordRecv, coordBroadcast, coordDecide, coordAlive, coordFaulty>>

PartAbortOnTimeout(p) ==
    /\ palive[p]
    /\ pfinal[p] = undecided
    /\ ~coordAlive
    /\ ~coordReqs[p]
    /\ pfinal' = [pfinal EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psentreq,
                   coordReqs, coordRecv, coordBroadcast, coordDecide, coordAlive, coordFaulty>>

PartDecide(p) ==
    /\ palive[p]
    /\ pfinal[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ pfinal' = [pfinal EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED <<pvote, palive, pfaulty, psentreq,
                   coordReqs, coordRecv, coordBroadcast, coordDecide, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ palive[p]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, pfinal, psentreq,
                   coordReqs, coordRecv, coordBroadcast, coordDecide, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : CoordSendReq(p)
    \/ \E p \in participants : CoordReceive(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnVote(p)
    \/ \E p \in participants : PartAbortOnTimeout(p)
    \/ \E p \in participants : PartDecide(p)
    \/ \E p \in participants : PartDie(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : PartSendVote(p))
    /\ WF_vars(\E p \in participants : PartAbortOnVote(p))
    /\ WF_vars(\E p \in participants : PartDecide(p))
    /\ WF_vars(\E p \in participants : PartAbortOnTimeout(p))

Agreement ==
    \A p, q \in participants :
        ~(pfinal[p] = commit /\ pfinal[q] = abort)

CommitValidity ==
    \A p \in participants : pfinal[p] = commit => (\A q \in participants : pvote[q] = yes)

AbortValidity ==
    \A p \in participants : pfinal[p] = abort =>
        (\E q \in participants : pvote[q] = no) \/ (\E q \in participants : pfaulty[q])
            \/ coordFaulty

Irreversibility ==
    \A p \in participants :
        /\ (pfinal[p] = commit) ~> (pfinal[p] = commit)
        /\ (pfinal[p] = abort) ~> (pfinal[p] = abort)

EventualDecision ==
    <>(\A p \in participants : pfinal[p] # undecided \/ coordFaulty \/ \E q \in participants : pfaulty[q])

Properties == Agreement /\ CommitValidity /\ AbortValidity /\ Irreversibility

====