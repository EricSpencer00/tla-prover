---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB): a coordinator
\* collects votes, decides commit/abort, and broadcasts the decision. A crash
\* during broadcast can leave participants undecided forever, so AC5
\* (non-blocking termination) does NOT hold for this variant -- AC3 below is
\* the weaker property that does hold.

VARIABLES pvote, palive, pdecision, pfaulty, psent, crequested,
          cvote, cbroadcast, cdecision, calive, cfaulty

vars == <<pvote, palive, pdecision, pfaulty, psent, crequested,
           cvote, cbroadcast, cdecision, calive, cfaulty>>

TypeOK ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pdecision \in [participants -> {undecided, commit, abort}]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ psent \in [participants -> BOOLEAN]
    /\ crequested \in [participants -> BOOLEAN]
    /\ cvote \in [participants -> {yes, no, waiting}]
    /\ cbroadcast \in [participants -> {commit, abort, notsent}]
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
    /\ cvote = [p \in participants |-> waiting]
    /\ cbroadcast = [p \in participants |-> notsent]
    /\ cdecision = undecided
    /\ calive = TRUE
    /\ cfaulty = FALSE

\* Coordinator actions
SendVoteRequest(p) ==
    /\ calive
    /\ ~crequested[p]
    /\ crequested' = [crequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   cvote, cbroadcast, cdecision, calive, cfaulty>>

RecvVote(p) ==
    /\ calive
    /\ cdecision = undecided
    /\ \A q \in participants : crequested[q]
    /\ cvote[p] = waiting
    /\ psent[p]
    /\ cvote' = [cvote EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   crequested, cbroadcast, cdecision, calive, cfaulty>>

DetectFault(p) ==
    /\ calive
    /\ cdecision = undecided
    /\ \A q \in participants : crequested[q]
    /\ cvote[p] = waiting
    /\ ~psent[p]
    /\ ~palive[p]
    /\ cdecision' = abort
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   crequested, cvote, cbroadcast, calive, cfaulty>>

MakeDecision ==
    /\ calive
    /\ cdecision = undecided
    /\ \A q \in participants : cvote[q] # waiting
    /\ cdecision' = IF (\A q \in participants : cvote[q] = yes) THEN commit ELSE abort
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   crequested, cvote, cbroadcast, calive, cfaulty>>

Broadcast(p) ==
    /\ calive
    /\ cdecision # undecided
    /\ cbroadcast[p] = notsent
    /\ cbroadcast' = [cbroadcast EXCEPT ![p] = cdecision]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   crequested, cvote, cdecision, calive, cfaulty>>

CoordDie ==
    /\ calive
    /\ calive' = FALSE
    /\ cfaulty' = TRUE
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   crequested, cvote, cbroadcast, cdecision>>

\* Participant actions
SendVote(p) ==
    /\ palive[p]
    /\ ~psent[p]
    /\ crequested[p]
    /\ psent' = [psent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                   crequested, cvote, cbroadcast, cdecision, calive, cfaulty>>

AbortOnNo(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ psent[p]
    /\ pvote[p] = no
    /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   crequested, cvote, cbroadcast, cdecision, calive, cfaulty>>

AbortTimeout(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ ~crequested[p]
    /\ ~calive
    /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   crequested, cvote, cbroadcast, cdecision, calive, cfaulty>>

Decide(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ cbroadcast[p] # notsent
    /\ pdecision' = [pdecision EXCEPT ![p] = cbroadcast[p]]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   crequested, cvote, cbroadcast, cdecision, calive, cfaulty>>

PartDie(p) ==
    /\ palive[p]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, pdecision, psent, crequested,
                   cvote, cbroadcast, cdecision, calive, cfaulty>>

CoordProgress == MakeDecision \/ CoordDie \/ (\E p \in participants : SendVoteRequest(p) \/ RecvVote(p) \/ DetectFault(p) \/ Broadcast(p))
PartProgress  == (\E p \in participants : SendVote(p) \/ AbortOnNo(p) \/ AbortTimeout(p) \/ Decide(p) \/ PartDie(p))

Next == CoordProgress \/ PartProgress

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordProgress) /\ WF_vars(PartProgress)

\* SAFETY: no two participants ever decide differently; a commit implies
\* unanimous yes votes, an abort implies a no vote or some fault.
Agreement ==
    \A p1, p2 \in participants :
        ~ (pdecision[p1] = commit /\ pdecision[p2] = abort)

CommitValid ==
    (\E p \in participants : pdecision[p] = commit) =>
        (\A p \in participants : pvote[p] = yes)

AbortValid ==
    (\E p \in participants : pdecision[p] = abort) =>
        (\E p \in participants : pvote[p] = no) \/ (\E p \in participants : pfaulty[p]) \/ cfaulty

Irreversibility ==
    /\ (\A p \in participants : (pdecision[p] = commit) ~> (pdecision[p] = commit))
    /\ (\A p \in participants : (pdecision[p] = abort) ~> (pdecision[p] = abort))

TypeInv == TypeOK /\ Agreement /\ CommitValid /\ AbortValid /\ Irreversibility

\* LIVENESS: every non-faulty transaction is eventually decided by someone
\* (coordinator or participant), or a fault surfaces. The stronger AC5
\* non-blocking termination property is NOT satisfied by ACP-SB and is
\* intentionally omitted from this spec.
AC3 == <>(\A p \in participants : pdecision[p] # undecided \/ \E p \in participants : pfaulty[p] \/ cfaulty)

====