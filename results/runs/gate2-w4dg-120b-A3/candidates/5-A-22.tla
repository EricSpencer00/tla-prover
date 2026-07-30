---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ coordAsked \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ coordAsked = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendRequest(p) ==
    /\ coordAlive
    /\ ~coordAsked[p]
    /\ coordAsked' = [coordAsked EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordAsked[p]
    /\ coordRecv[p] = waiting
    /\ pSent[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordAsked, coordSent, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordAsked[p]
    /\ coordRecv[p] = waiting
    /\ ~pAlive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordAsked, coordRecv, coordSent, coordAlive, coordFaulty>>

Decide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordRecv[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordAsked, coordRecv, coordSent, coordAlive, coordFaulty>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordAsked, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordAsked, coordRecv, coordSent, coordDecision, coordFaulty>>

SendVote(p) ==
    /\ pAlive[p]
    /\ coordAsked[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnNo(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnNoRequest(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~coordAsked[p]
    /\ ~pAlive[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent, coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : SendRequest(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ Decide
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnNo(p)
    \/ \E p \in participants : AbortOnNoRequest(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars

DecisionCoherent ==
    \A p, q \in participants :
        (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE

CommitValid ==
    \A p \in participants : pDecision[p] = commit => (\A q \in participants : pVote[q] = yes)

AbortValid ==
    \A p \in participants :
        pDecision[p] = abort =>
            \/ \E q \in participants : pVote[q] = no
            \/ \E q \in participants : pFaulty[q]
            \/ coordFaulty

Irreversible ==
    \A p \in participants :
        (pDecision[p] = commit) ~> (pDecision[p] = commit)
        /\ (pDecision[p] = abort) ~> (pDecision[p] = abort)

DecideEventually ==
    <>(\A p \in participants : pDecision[p] # undecided \/
                     pFaulty[p] \/ coordFaulty)

====