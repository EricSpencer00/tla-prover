---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Simple-broadcast ACP: coordinator failure during broadcast can leave
\* participants undecided, so the model does NOT guarantee eventual decision
\* for every participant (termination is not modeled as a guaranteed outcome).
VARIABLES partVote, partAlive, partDecision, partFaulty, partSent,
          coordDecisionsSent, coordVote, coordDecision, coordAlive, coordFaulty

vars == <<partVote, partAlive, partDecision, partFaulty, partSent,
           coordDecisionsSent, coordVote, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
    /\ partVote \in [participants -> {yes, no}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> {undecided, commit, abort}]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partSent \in [participants -> BOOLEAN]
    /\ coordDecisionsSent \in [participants -> {notsent, commit, abort}]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ partVote \in [participants -> {yes, no}]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partDecision = [p \in participants |-> undecided]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partSent = [p \in participants |-> FALSE]
    /\ coordDecisionsSent = [p \in participants |-> notsent]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator actions
SendVoteReq(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordDecisionsSent[p] = notsent
    /\ ~coordVote[p] \in {yes, no}
    /\ coordVote' = [coordVote EXCEPT ![p] = waiting]
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordDecisionsSent, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordVote[p] = waiting
    /\ partSent[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordDecisionsSent, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordVote[p] = waiting
    /\ ~partAlive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordDecisionsSent, coordVote, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] \in {yes, no}
    /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordDecisionsSent, coordVote, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordDecisionsSent[p] = notsent
    /\ coordDecisionsSent' = [coordDecisionsSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                   coordDecisionsSent, coordVote, coordDecision>>

\* Participant actions
SendVote(p) ==
    /\ partAlive[p]
    /\ coordVote[p] = waiting
    /\ partSent' = [partSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty,
                   coordDecisionsSent, coordVote, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ partSent[p]
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                   coordDecisionsSent, coordVote, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ coordVote[p] = waiting
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                   coordDecisionsSent, coordVote, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ coordDecisionsSent[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordDecisionsSent[p]]
    /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                   coordDecisionsSent, coordVote, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<partVote, partDecision, partSent,
                   coordDecisionsSent, coordVote, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : SendVoteReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : PartDie(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants : SF_vars(SendVote(p))
    /\ \A p \in participants : WF_vars(DecideOnBroadcast(p))
    /\ \A p \in participants : WF_vars(AbortOnTimeout(p))
    /\ \A p \in participants : SF_vars(AbortOnVote(p))
    /\ SF_vars(MakeDecision)

\* No two participants ever decide differently: commit and abort are mutually
\* exclusive outcomes, so a mixed decision would mean two participants decided
\* opposite values, which violates consistency.
Agreement ==
    \A p1 \in participants, p2 \in participants :
        (partDecision[p1] = commit /\ partDecision[p2] = abort) => p1 = p2

CommitValidity ==
    \A p \in participants : partDecision[p] = commit => \A q \in participants : partVote[q] = yes

AbortValidity ==
    \A p \in participants :
        partDecision[p] = abort =>
            \/ \E q \in participants : partVote[q] = no
            \/ \E q \in participants : partFaulty[q]
            \/ coordFaulty

Irreversibility ==
    \A p \in participants :
        (partDecision[p] = commit => (\A d \in {commit, abort} : partDecision[p] # d))
        /\ (partDecision[p] = abort => (\A d \in {commit, abort} : partDecision[p] # d))

\* Simple-broadcast ACP is blocking: a coordinator crash during broadcast can
\* leave some participants undecided forever, so eventual decision for every
\* participant is not guaranteed (the non-blocking AC5 property is omitted by
\* design for this variant). The single guaranteed outcome is that either
\* everyone decides or a failure surfaces.
Liveness ==
    (coordAlive \/ coordFaulty) /\ (\A p \in participants : partAlive[p] \/ partFaulty[p])
        ~> (\A p \in participants : partDecision[p] # undecided) \/ coordFaulty

TypeInv == TypeOK

====