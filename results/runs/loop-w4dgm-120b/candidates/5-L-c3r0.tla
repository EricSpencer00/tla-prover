---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator always ahead of participants on the decision front, so a
\* participant can only unilaterally abort when its own vote is no.
VARIABLES pvote, palive, pdecision, pfaulty, psent, creqsent,
          cvote, cbroadcast, cdecision, calive, cfaulty

vars == <<pvote, palive, pdecision, pfaulty, psent, creqsent,
           cvote, cbroadcast, cdecision, calive, cfaulty>>

TypeOK ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pdecision \in [participants -> {undecided, commit, abort}]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ psent \in [participants -> BOOLEAN]
    /\ creqsent \in [participants -> BOOLEAN]
    /\ cvote \in [participants -> {yes, no, waiting}]
    /\ cbroadcast \in [participants -> {commit, abort, notsent}]
    /\ cdecision \in {undecided, commit, abort}
    /\ calive \in BOOLEAN
    /\ cfaulty \in BOOLEAN

Init ==
    /\ \E v \in {yes, no} : pvote = [p \in participants |-> v]
    /\ palive = [p \in participants |-> TRUE]
    /\ pdecision = [p \in participants |-> undecided]
    /\ pfaulty = [p \in participants |-> FALSE]
    /\ psent = [p \in participants |-> FALSE]
    /\ creqsent = [p \in participants |-> FALSE]
    /\ cvote = [p \in participants |-> waiting]
    /\ cbroadcast = [p \in participants |-> notsent]
    /\ cdecision = undecided
    /\ calive = TRUE
    /\ cfaulty = FALSE

\* Coordinator requests votes from all participants (one broadcast strand
\* at a time, so a failure while broadcasting is fatal to progress).
SendReq ==
    /\ calive
    /\ \E p \in participants :
         /\ ~creqsent[p]
         /\ creqsent' = [creqsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   cvote, cbroadcast, cdecision, calive, cfaulty>>

RecvVote ==
    /\ calive
    /\ cdecision = undecided
    /\ \E p \in participants :
         /\ creqsent[p]
         /\ cvote[p] = waiting
         /\ psent[p]
         /\ cvote' = [cvote EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   creqsent, cbroadcast, cdecision, calive, cfaulty>>

CoordinatorDetectFault ==
    /\ calive
    /\ cdecision = undecided
    /\ \A p \in participants : creqsent[p]
    /\ \E p \in participants :
         /\ cvote[p] = waiting
         /\ ~palive[p]
         /\ ~psent[p]
    /\ cdecision' = abort
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   creqsent, cvote, cbroadcast, calive, cfaulty>>

MakeDecision ==
    /\ calive
    /\ cdecision = undecided
    /\ \A p \in participants : cvote[p] # waiting
    /\ cdecision' = IF \A p \in participants : cvote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   creqsent, cvote, cbroadcast, calive, cfaulty>>

\* Simple broadcast: a single strand, one participant at a time.
BroadcastDecision ==
    /\ calive
    /\ cdecision # undecided
    /\ \E p \in participants :
         /\ cbroadcast[p] = notsent
         /\ cbroadcast' = [cbroadcast EXCEPT ![p] = cdecision]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   creqsent, cvote, cdecision, calive, cfaulty>>

CoordinatorDie ==
    /\ calive
    /\ calive' = FALSE
    /\ cfaulty' = TRUE
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   creqsent, cvote, cbroadcast, cdecision>>

SendVote ==
    /\ palive
    /\ \E p \in participants :
         /\ creqsent[p]
         /\ ~psent[p]
         /\ psent' = [psent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                   creqsent, cvote, cbroadcast, cdecision, calive, cfaulty>>

AbortOnVote ==
    /\ palive
    /\ \E p \in participants :
         /\ psent[p]
         /\ pdecision[p] = undecided
         /\ pvote[p] = no
         /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, palive, pfaulty, psent,
                   creqsent, cvote, cbroadcast, cdecision, calive, cfaulty>>

AbortOnTimeoutReq ==
    /\ palive
    /\ ~calive
    /\ \E p \in participants :
         /\ ~creqsent[p]
         /\ pdecision[p] = undecided
         /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   creqsent, cvote, cbroadcast, cdecision, calive, cfaulty>>

DecideOnBroadcast ==
    /\ palive
    /\ \E p \in participants :
         /\ cbroadcast[p] # notsent
         /\ pdecision[p] = undecided
         /\ pdecision' = [pdecision EXCEPT ![p] = cbroadcast[p]]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   creqsent, cvote, cbroadcast, cdecision, calive, cfaulty>>

ParticipantDie ==
    /\ \E p \in participants :
         /\ palive[p]
         /\ palive' = [palive EXCEPT ![p] = FALSE]
         /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, pdecision, psent,
                   creqsent, cvote, cbroadcast, cdecision, calive, cfaulty>>

Next ==
    \/ SendReq \/ RecvVote \/ CoordinatorDetectFault \/ MakeDecision
    \/ BroadcastDecision \/ CoordinatorDie \/ SendVote
    \/ AbortOnVote \/ AbortOnTimeoutReq \/ DecideOnBroadcast \/ ParticipantDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordinatorDie)
    /\ WF_vars(ParticipantDie)
    /\ \A p \in participants :
         /\ WF_vars(SendVote)
         /\ WF_vars(AbortOnVote)
         /\ WF_vars(DecideOnBroadcast)

\* Commitment is only consistent if everyone voted yes; abort otherwise.
AllDecideTheSame ==
    \A p, q \in participants :
        (pdecision[p] = commit /\ pdecision[q] = abort) => FALSE

AbortValid ==
    \A p \in participants :
        (pdecision[p] = abort =>
            (\E q \in participants : pvote[q] = no) \/ (\E q \in participants : pfaulty[q]) \/ cfaulty)

DecideAtMostOnce ==
    \A p \in participants :
        /\ (pdecision[p] = commit => (pdecision[p] \in [pdecision EXCEPT ![p] = commit]))
        /\ (pdecision[p] = abort => (pdecision[p] \in [pdecision EXCEPT ![p] = abort]))

EventualDecision ==
    <>(\A p \in participants : pdecision[p] # undecided) \/ (\E p \in participants : pfaulty[p]) \/ cfaulty

====