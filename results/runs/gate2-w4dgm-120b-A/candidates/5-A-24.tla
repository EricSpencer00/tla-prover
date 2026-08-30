---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The simple broadcast variant blocks if the coordinator dies mid-broadcast, so
\* the liveness property AC5 (everyone eventually decides) is NOT satisfied here;
\* ACAgree and ACDecide capture safety and the conditional liveness AC3.
VARIABLES pvote, palive, pdecided, pfaulty, psent, crequested, cvote,
          csent, cdecided, calive, cfaulty

vars == <<pvote, palive, pdecided, pfaulty, psent, crequested, cvote,
           csent, cdecided, calive, cfaulty>>

TypeInv ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pdecided \in [participants -> {undecided, commit, abort}]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ psent \in [participants -> BOOLEAN]
    /\ crequested \in [participants -> BOOLEAN]
    /\ cvote \in [participants -> {yes, no, waiting}]
    /\ csent \in [participants -> {commit, abort, notsent}]
    /\ cdecided \in {commit, abort, undecided}
    /\ calive \in BOOLEAN
    /\ cfaulty \in BOOLEAN

Init ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive = [p \in participants |-> TRUE]
    /\ pdecided = [p \in participants |-> undecided]
    /\ pfaulty = [p \in participants |-> FALSE]
    /\ psent = [p \in participants |-> FALSE]
    /\ crequested = [p \in participants |-> FALSE]
    /\ cvote = [p \in participants |-> waiting]
    /\ csent = [p \in participants |-> notsent]
    /\ cdecided = undecided
    /\ calive = TRUE
    /\ cfaulty = FALSE

\* Coordinator actions ---------------------------------------------------------
RequestVote(p) ==
    /\ calive
    /\ ~crequested[p]
    /\ crequested' = [crequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecided, pfaulty, psent,
                   cvote, csent, cdecided, calive, cfaulty>>

ReceiveVote(p) ==
    /\ calive
    /\ cdecided = undecided
    /\ \A q \in participants : crequested[q]
    /\ cvote[p] = waiting
    /\ psent[p]
    /\ cvote' = [cvote EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED <<pvote, palive, pdecided, pfaulty, psent,
                   crequested, csent, cdecided, calive, cfaulty>>

DetectFault(p) ==
    /\ calive
    /\ cdecided = undecided
    /\ \A q \in participants : crequested[q]
    /\ cvote[p] = waiting
    /\ ~palive[p]
    /\ ~psent[p]
    /\ cdecided' = abort
    /\ UNCHANGED <<pvote, palive, pdecided, pfaulty, psent,
                   crequested, cvote, csent, calive, cfaulty>>

Decide ==
    /\ calive
    /\ cdecided = undecided
    /\ \A p \in participants : cvote[p] # waiting
    /\ cdecided' = IF \A p \in participants : cvote[p] = yes
                   THEN commit ELSE abort
    /\ UNCHANGED <<pvote, palive, pdecided, pfaulty, psent,
                   crequested, cvote, csent, calive, cfaulty>>

Broadcast(p) ==
    /\ calive
    /\ cdecided # undecided
    /\ csent[p] = notsent
    /\ csent' = [csent EXCEPT ![p] = cdecided]
    /\ UNCHANGED <<pvote, palive, pdecided, pfaulty, psent,
                   crequested, cvote, cdecided, calive, cfaulty>>

CoordinateDie ==
    /\ calive
    /\ calive' = FALSE
    /\ cfaulty' = TRUE
    /\ UNCHANGED <<pvote, palive, pdecided, pfaulty, psent,
                   crequested, cvote, csent, cdecided>>

\* Participant actions ---------------------------------------------------------
SendVote(p) ==
    /\ palive[p]
    /\ crequested[p]
    /\ ~psent[p]
    /\ psent' = [psent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecided, pfaulty,
                   crequested, cvote, csent, cdecided, calive, cfaulty>>

AbortOnVote(p) ==
    /\ palive[p]
    /\ pdecided[p] = undecided
    /\ psent[p]
    /\ pvote[p] = no
    /\ pdecided' = [pdecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   crequested, cvote, csent, cdecided, calive, cfaulty>>

AbortOnTimeout(p) ==
    /\ ~calive
    /\ \A q \in participants : ~crequested[q]
    /\ pdecided[p] = undecided
    /\ pdecided' = [pdecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   crequested, cvote, csent, cdecided, calive, cfaulty>>

DecideOnBroadcast(p) ==
    /\ palive[p]
    /\ pdecided[p] = undecided
    /\ csent[p] # notsent
    /\ pdecided' = [pdecided EXCEPT ![p] = csent[p]]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   crequested, cvote, csent, cdecided, calive, cfaulty>>

ParticipantDie(p) ==
    /\ palive[p]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, pdecided, psent,
                   crequested, cvote, csent, cdecided, calive, cfaulty>>

\* Fairness: progress steps (everything except death) are weakly fair, which
\* is what rules out runs that stay forever stuck on a vote or decision.
CoordStep == \E p \in participants : RequestVote(p) \/ ReceiveVote(p) \/ DetectFault(p)
ParticipantStep == \E p \in participants : SendVote(p) \/ AbortOnVote(p)

Next ==
    \/ \E p \in participants : RequestVote(p) \/ ReceiveVote(p) \/ DetectFault(p)
                              \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p)
                              \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p)
    \/ Decide
    \/ CoordinateDie
    \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CoordStep)
        /\ WF_vars(Decide)
        /\ SF_vars(ParticipantStep)

\* Safety: a commit can never be observed alongside a contradictory abort.
AgreementConsistent ==
    \A p, q \in participants :
        (pdecided[p] = commit /\ pdecided[q] = abort) => FALSE

\* A commit needs unanimous yes; an abort needs a no vote or a crash.
CommitRequiresUnanimity ==
    \A p \in participants :
        (pdecided[p] = commit) => (\A q \in participants : pvote[q] = yes)

AbortNotWithoutReason ==
    \A p \in participants :
        (pdecided[p] = abort) =>
            (\E q \in participants : pvote[q] = no \/ pfaulty[q] \/ cfaulty)

IrreversibleDecision ==
    \A p \in participants :
        /\ (pdecided[p] = commit) => (pdecided' = [pdecided EXCEPT ![p] = commit])
        /\ (pdecided[p] = abort)  => (pdecided' = [pdecided EXCEPT ![p] = abort])

\* Liveness: every transaction eventually resolves or is witnessed crashing.
EventualResolution ==
    <>(\A p \in participants : pdecided[p] # undecided \/ \E p \in participants : pfaulty[p] \/ cfaulty)

====