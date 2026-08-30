---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, psent,
          coasked, crewarded, cdecision, calive, cfaulty

vars == <<pvote, palive, pdecision, pfaulty, psent,
          coasked, crewarded, cdecision, calive, cfaulty>>

TypeOK ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pdecision \in [participants -> {undecided, commit, abort}]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ psent \in [participants -> BOOLEAN]
    /\ coasked \in [participants -> BOOLEAN]
    /\ crewarded \in [participants -> {waiting, notsent} \cup {commit, abort}]
    /\ cdecision \in {undecided, commit, abort}
    /\ calive \in BOOLEAN
    /\ cfaulty \in BOOLEAN

Init ==
    /\ \E v \in {yes, no} : pvote = [p \in participants |-> v]
    /\ palive = [p \in participants |-> TRUE]
    /\ pdecision = [p \in participants |-> undecided]
    /\ pfaulty = [p \in participants |-> FALSE]
    /\ psent = [p \in participants |-> FALSE]
    /\ coasked = [p \in participants |-> FALSE]
    /\ crewarded = [p \in participants |-> waiting]
    /\ cdecision = undecided
    /\ calive = TRUE
    /\ cfaulty = FALSE

SendVoteRequest(p) ==
    /\ calive
    /\ ~coasked[p]
    /\ coasked' = [coasked EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   crewarded, cdecision, calive, cfaulty>>

ReceiveVote(p) ==
    /\ calive
    /\ cdecision = undecided
    /\ coasked[p]
    /\ crewarded[p] = waiting
    /\ psent[p]
    /\ crewarded' = [crewarded EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   coasked, cdecision, calive, cfaulty>>

DetectParticipantFault(p) ==
    /\ calive
    /\ cdecision = undecided
    /\ coasked[p]
    /\ crewarded[p] = waiting
    /\ ~palive[p]
    /\ ~psent[p]
    /\ cdecision' = abort
    /\ crewarded' = [crewarded EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   coasked, calive, cfaulty>>

MakeDecision ==
    /\ calive
    /\ cdecision = undecided
    /\ \A p \in participants : coasked[p]
    /\ \A p \in participants : psent[p]
    /\ cdecision' = (IF \A p \in participants : pvote[p] = yes THEN commit ELSE abort)
    /\ crewarded' = [p \in participants |->
                       IF cdecision' = commit THEN commit ELSE IF cdecision' = abort THEN abort ELSE waiting]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent, coasked, calive, cfaulty>>

BroadcastDecision(p) ==
    /\ calive
    /\ cdecision # undecided
    /\ crewarded[p] = notsent
    /\ crewarded' = [crewarded EXCEPT ![p] = cdecision]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   coasked, cdecision, calive, cfaulty>>

CoordDie ==
    /\ calive
    /\ calive' = FALSE
    /\ cfaulty' = TRUE
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psent,
                   coasked, crewarded, cdecision>>

SendVote(p) ==
    /\ palive[p]
    /\ coasked[p]
    /\ ~psent[p]
    /\ psent' = [psent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                   coasked, crewarded, cdecision, calive, cfaulty>>

ParticipantAbortOnVote(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ psent[p]
    /\ pvote[p] = no
    /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   coasked, crewarded, cdecision, calive, cfaulty>>

ParticipantAbortOnTimeout(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ ~coasked[p]
    /\ cfaulty
    /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   coasked, crewarded, cdecision, calive, cfaulty>>

DecideFromCoordinator(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ crewarded[p] \in {commit, abort}
    /\ pdecision' = [pdecision EXCEPT ![p] = crewarded[p]]
    /\ UNCHANGED <<pvote, palive, pfaulty, psent,
                   coasked, crewarded, cdecision, calive, cfaulty>>

ParticipantDie(p) ==
    /\ palive[p]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, pdecision, psent,
                   coasked, crewarded, cdecision, calive, cfaulty>>

CoordProgress ==
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)

ParticipantProgress ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : ParticipantAbortOnVote(p)
    \/ \E p \in participants : ParticipantAbortOnTimeout(p)
    \/ \E p \in participants : DecideFromCoordinator(p)

Next ==
    \/ \E p \in participants : SendVoteRequest(p) \/ ReceiveVote(p)
                             \/ DetectParticipantFault(p) \/ BroadcastDecision(p)
                             \/ SendVote(p) \/ ParticipantAbortOnVote(p)
                             \/ ParticipantAbortOnTimeout(p) \/ DecideFromCoordinator(p)
                             \/ ParticipantDie(p)
    \/ MakeDecision
    \/ CoordDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(CoordProgress)
    /\ SF_vars(ParticipantProgress)

Agreement ==
    \A p1, p2 \in participants :
        ~(pdecision[p1] = commit /\ pdecision[p2] = abort)

CommitValidity ==
    \A p \in participants : pdecision[p] = commit => \A q \in participants : pvote[q] = yes

AbortValidity ==
    \A p \in participants :
        pdecision[p] = abort =>
            \/ \E q \in participants : pvote[q] = no
            \/ \E q \in participants : ~palive[q]
            \/ ~calive

Irrevocability ==
    \A p \in participants :
        /\ (pdecision[p] = commit => [q \in participants |-> pdecision[q]][p] = commit)
        /\ (pdecision[p] = abort => [q \in participants |-> pdecision[q]][p] = abort)

TerminationLiveness ==
    <>(\A p \in participants : pdecision[p] # undecided \/ ~calive \/ ~\A q \in participants : palive[q])

TypeInv == TypeOK

====