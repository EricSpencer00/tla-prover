---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision, coordSent, coordReceived,
          pAlive, pFaulty, pVote, pDecision, pSentVote, pRecv

vars == <<coordAlive, coordFaulty, coordDecision, coordSent, coordReceived,
           pAlive, pFaulty, pVote, pDecision, pSentVote, pRecv>>

TypeInv ==
    /\ coordAlive \in {TRUE, FALSE}
    /\ coordFaulty \in {TRUE, FALSE}
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSent \in [participants -> {notsent, sent}]
    /\ coordReceived \in [participants -> {waiting, yes, no}]
    /\ pAlive \in [participants -> {TRUE, FALSE}]
    /\ pFaulty \in [participants -> {FALSE, TRUE}]
    /\ pVote \in [participants -> {yes, no}]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pRecv \in [participants -> {notsent, sent}]

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordReceived = [p \in participants |-> waiting]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> IF CHOOSE b \in {yes, no} : TRUE THEN yes ELSE no]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ pRecv = [p \in participants |-> notsent]

SendReq(p) ==
    /\ coordAlive
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = sent]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReceived,
                   pAlive, pFaulty, pVote, pDecision, pSentVote, pRecv>>

RecvVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordReceived[p] = waiting
    /\ coordSent[p] = sent
    /\ pSentVote[p]
    /\ coordReceived' = [coordReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                   pAlive, pFaulty, pVote, pDecision, pSentVote, pRecv>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSent[p] = sent
    /\ coordReceived[p] = waiting
    /\ ~pAlive[p]
    /\ coordReceived' = [coordReceived EXCEPT ![p] = no]
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSent,
                   pAlive, pFaulty, pVote, pDecision, pSentVote, pRecv>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordReceived[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordReceived[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordReceived,
                   pAlive, pFaulty, pVote, pDecision, pSentVote, pRecv>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ pRecv[p] = notsent
    /\ pRecv' = [pRecv EXCEPT ![p] = sent]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordReceived,
                   pAlive, pFaulty, pVote, pDecision, pSentVote>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordSent, coordReceived,
                   pAlive, pFaulty, pVote, pDecision, pSentVote, pRecv>>

SendVote(p) ==
    /\ pAlive[p]
    /\ coordSent[p] = sent
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordReceived,
                   pAlive, pFaulty, pVote, pDecision, pRecv>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordReceived,
                   pAlive, pFaulty, pVote, pSentVote, pRecv>>

AbortOnNoReq(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordSent[p] = notsent
    /\ ~coordAlive
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordReceived,
                   pAlive, pFaulty, pVote, pSentVote, pRecv>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pRecv[p] = sent
    /\ pDecision' = [pDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordReceived,
                   pAlive, pFaulty, pVote, pSentVote, pRecv>>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordReceived,
                   pVote, pDecision, pSentVote, pRecv>>

Next ==
    \/ MakeDecision
    \/ CoordDie
    \/ \E p \in participants :
           \/ SendReq(p) \/ RecvVote(p) \/ DetectFault(p) \/ Broadcast(p)
           \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnNoReq(p)
           \/ DecideOnBroadcast(p) \/ ParticipantDie(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendReq(p))
    /\ WF_vars(\E p \in participants : RecvVote(p))
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))

Agree ==
    \A p, q \in participants :
        (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE

CommitValid == \E p \in participants : pDecision[p] = commit => \A q \in participants : coordReceived[q] = yes

AbortValid ==
    \E p \in participants :
        pDecision[p] = abort =>
            \/ \E q \in participants : coordReceived[q] = no
            \/ \E q \in participants : pFaulty[q]
            \/ coordFaulty

Irrevocable == \A p \in participants : (pDecision[p] = commit) ~> (pDecision[p] = commit)

Terminate ==
    \/ \A p \in participants : pDecision[p] # undecided
    \/ \E p \in participants : pFaulty[p]
    \/ coordFaulty

====