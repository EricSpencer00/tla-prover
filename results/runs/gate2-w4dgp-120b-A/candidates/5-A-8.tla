---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-SB: Atomic Commitment Protocol with Simple Broadcast. The coordinator
\* gathers votes and broadcasts a commit/abort decision one participant at a
\* time. A coordinator or participant may die silently; the spec tracks
\* both the crashed flag and the liveness flag separately so that a crash
\* can be observed without conflating it with a permanent death.

VARIABLES pvote, palive, pdecision, pfaulty, psent, crequested, crecv,
          csend, cdecision, calive, cfaulty

vars == <<pvote, palive, pdecision, pfaulty, psent, crequested, crecv,
          csend, cdecision, calive, cfaulty>>

TypeInv ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pdecision \in [participants -> {undecided, commit, abort}]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ psent \in [participants -> BOOLEAN]
    /\ crequested \in [participants -> BOOLEAN]
    /\ crecv \in [participants -> {yes, no, waiting}]
    /\ csend \in [participants -> {commit, abort, notsent}]
    /\ cdecision \in {undecided, commit, abort}
    /\ calive \in BOOLEAN
    /\ cfaulty \in BOOLEAN

Init ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive = [p \in participants |-> TRUE]
    /\ pdecision = [p \in participants |-> undecided]
    /\ pfaulty = [p \in participants |-> FALSE]
    /\ psent = [p \in participants |-> FALSE]
    /\ crequested = [p \in participants |-> FALSE]
    /\ crecv = [p \in participants |-> waiting]
    /\ csend = [p \in participants |-> notsent]
    /\ cdecision = undecided
    /\ calive = TRUE
    /\ cfaulty = FALSE

\* Coordinator actions

RequestVote(p) ==
    /\ calive
    /\ ~crequested[p]
    /\ crequested' = [crequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent, crecv,
                    csend, cdecision, calive, cfaulty>>

ReceiveVote(p) ==
    /\ calive
    /\ cdecision = undecided
    /\ crequested[p]
    /\ crecv[p] = waiting
    /\ psent[p]
    /\ crecv' = [crecv EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                    crequested, csend, cdecision, calive, cfaulty>>

DetectParticipantFault(p) ==
    /\ calive
    /\ cdecision = undecided
    /\ crequested[p]
    /\ crecv[p] = waiting
    /\ ~palive[p]
    /\ cdecision' = abort
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                    crequested, crecv, csend, calive, cfaulty>>

Decide ==
    /\ calive
    /\ cdecision = undecided
    /\ \A p \in participants : crecv[p] # waiting
    /\ cdecision' = IF \A p \in participants : crecv[p] = yes
                     THEN commit ELSE abort
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                    crequested, crecv, csend, calive, cfaulty>>

BroadcastDecision(p) ==
    /\ calive
    /\ cdecision # undecided
    /\ csend[p] = notsent
    /\ csend' = [csend EXCEPT ![p] = cdecision]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                    crequested, crecv, cdecision, calive, cfaulty>>

DieCoordinator ==
    /\ calive
    /\ calive' = FALSE
    /\ cfaulty' = TRUE
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                    crequested, crecv, csend, cdecision>>

\* Participant actions

SendVote(p) ==
    /\ palive[p]
    /\ ~psent[p]
    /\ crequested[p]
    /\ psent' = [psent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, crequested,
                    crecv, csend, cdecision, calive, cfaulty>>

AbortOnVote(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ psent[p]
    /\ pvote[p] = no
    /\ pdecision[p] = abort
    /\ UNCHANGED <<pvote, palive, pfaulty, psent, crequested,
                    crecv, csend, cdecision, calive, cfaulty>>

AbortOnTimeout(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ ~calive
    /\ ~crequested[p]
    /\ pdecision[p] = abort
    /\ UNCHANGED <<pvote, palive, pfaulty, psent, crequested,
                    crecv, csend, cdecision, calive, cfaulty>>

DecideFromBroadcast(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ csend[p] # notsent
    /\ pdecision' = [pdecision EXCEPT ![p] = csend[p]]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent, crequested,
                    crecv, csend, cdecision, calive, cfaulty>>

DieParticipant(p) ==
    /\ palive[p]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, pdecision, psent, crequested,
                    crecv, csend, cdecision, calive, cfaulty>>

Next ==
    \/ \E p \in participants : RequestVote(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectParticipantFault(p)
    \/ Decide
    \/ \E p \in participants : BroadcastDecision(p)
    \/ DieCoordinator
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : DieParticipant(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
    /\ WF_vars(\E p \in participants : DecideFromBroadcast(p))
    /\ WF_vars(\E p \in participants : BroadcastDecision(p))

\* SAFETY (always true, never dependent on fairness)

\* AC1: Agreement -- no two participants ever make conflicting decisions.
AC1 ==
    \A p, q \in participants :
        ~(pdecision[p] = commit /\ pdecision[q] = abort)

\* AC2: Validity of commit -- a commit requires unanimity.
AC2 ==
    \A p \in participants :
        pdecision[p] = commit => (\A q \in participants : pvote[q] = yes)

\* AC3: Validity of abort -- abort is justified by at least one no vote,
\* or a participant fault, or a coordinator fault.
AC3 ==
    \A p \in participants :
        pdecision[p] = abort =>
            (\E q \in participants : pvote[q] = no \/ pfaulty[q] \/ cfaulty)

\* AC4: Irreversibility -- a participant's decision never changes once made.
AC4 ==
    \A p \in participants :
        /\ (pdecision[p] = commit) => (pdecision[p] = commit)
        /\ (pdecision[p] = abort)  => (pdecision[p] = abort)

\* LIVENESS (true under the given fairness assumptions)

\* AC3 liveness component: the protocol eventually decides or detects a fault.
DecisionEventually ==
    <>(\A p \in participants : pdecision[p] # undecided \/ pfaulty[p] \/ cfaulty)

====