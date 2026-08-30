---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecided, coordVoteReq, coordW4, coordSent
Vote, pAlive, pFaulty, pDecided, pSent

vars == <<coordAlive, coordFaulty, coordDecided, coordVoteReq, coordW4, coordSent,
           Vote, pAlive, pFaulty, pDecided, pSent>>

TypeOK ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecided \in {undecided, commit, abort}
    /\ coordVoteReq \in [participants -> BOOLEAN]
    /\ coordW4 \in [participants -> {waiting} \cup {yes, no}]
    /\ coordSent \in [participants -> {notsent} \cup {commit, abort}]
    /\ Vote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecided \in [participants -> {undecided, commit, abort}]
    /\ pSent \in [participants -> BOOLEAN]

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecided = undecided
    /\ coordVoteReq = [p \in participants |-> FALSE]
    /\ coordW4 = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ Vote = [p \in participants |-> IF (p \in participants) THEN yes ELSE no]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecided = [p \in participants |-> undecided]
    /\ pSent = [p \in participants |-> FALSE]

VoteReq(p) ==
    /\ coordAlive
    /\ ~coordVoteReq[p]
    /\ coordVoteReq' = [coordVoteReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecided, coordW4, coordSent,
                   Vote, pAlive, pFaulty, pDecided, pSent>>

RecvCoordVote(p) ==
    /\ coordAlive
    /\ coordDecided = undecided
    /\ coordVoteReq[p]
    /\ coordW4[p] = waiting
    /\ pSent[p]
    /\ coordW4' = [coordW4 EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecided, coordVoteReq,
                   coordSent, Vote, pAlive, pFaulty, pDecided, pSent>>

DetectPtlFault(p) ==
    /\ coordAlive
    /\ coordDecided = undecided
    /\ coordVoteReq[p]
    /\ coordW4[p] = waiting
    /\ ~pAlive[p]
    /\ coordDecided' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordVoteReq, coordW4, coordSent,
                   Vote, pAlive, pFaulty, pDecided, pSent>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecided = undecided
    /\ \A p \in participants : coordW4[p] # waiting \/ ~coordVoteReq[p]
    /\ coordDecided' = IF \A p \in participants : coordW4[p] = yes
                       THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordVoteReq, coordW4, coordSent,
                   Vote, pAlive, pFaulty, pDecided, pSent>>

BroadcastCoord(p) ==
    /\ coordAlive
    /\ coordDecided # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecided]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecided, coordVoteReq,
                   coordW4, Vote, pAlive, pFaulty, pDecided, pSent>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecided, coordVoteReq, coordW4, coordSent,
                   Vote, pAlive, pFaulty, pDecided, pSent>>

SendVote(p) ==
    /\ pAlive[p]
    /\ coordVoteReq[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecided, coordVoteReq,
                   coordW4, coordSent, Vote, pAlive, pFaulty, pDecided>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ pSent[p]
    /\ Vote[p] = no
    /\ pDecided' = [pDecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecided, coordVoteReq,
                   coordW4, coordSent, Vote, pAlive, pFaulty, pSent>>

AbortOnCoordTimeout(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ ~coordAlive
    /\ ~coordVoteReq[p]
    /\ pDecided' = [pDecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecided, coordVoteReq,
                   coordW4, coordSent, Vote, pAlive, pFaulty, pSent>>

DecideCoordBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ coordSent[p] # notsent
    /\ pDecided' = [pDecided EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecided, coordVoteReq,
                   coordW4, coordSent, Vote, pAlive, pFaulty, pSent>>

PtlDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecided, coordVoteReq,
                   coordW4, coordSent, Vote, pDecided, pSent>>

CoordNext ==
    \/ \E p \in participants : VoteReq(p)
    \/ \E p \in participants : RecvCoordVote(p)
    \/ \E p \in participants : DetectPtlFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastCoord(p)
    \/ CoordDie

PtlNext ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnCoordTimeout(p)
    \/ \E p \in participants : DecideCoordBroadcast(p)
    \/ \E p \in participants : PtlDie(p)

Next == CoordNext \/ PtlNext

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordNext)
    /\ WF_vars(PtlNext)

AC1 == \A p, q \in participants : ~(pDecided[p] = commit /\ pDecided[q] = abort)
AC2 == (\E p \in participants : pDecided[p] = commit) => \A p \in participants : Vote[p] = yes
AC3 == (\E p \in participants : pDecided[p] = abort) =>
           (\E p \in participants : Vote[p] = no \/ pFaulty[p]) \/ coordFaulty
AC4 == \A p \in participants :
           /\ (pDecided[p] = commit) ~> (pDecided[p] = commit)
           /\ (pDecided[p] = abort) ~> (pDecided[p] = abort)

AC3Live ==
    <>(\A p \in participants : pDecided[p] # undecided \/ pFaulty[p]) \/ coordFaulty

TypeInv == TypeOK
====