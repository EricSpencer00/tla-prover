---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Inherited state from the base simple-broadcast variant: coordinator vote,
\* coordinator alive/faulty, coordinator broadcast/decision phase, participant
\* vote, participant alive/faulty, and participant decision (aggregated).
VARIABLES cvote, calive, cfaulty, cphase, cdecision, pvote, palive, pdecision

\* New per-participant forwarding table: for each participant a map from every
\* participant identifier to its forwarding status (not-sent, commit, abort),
\* tracking what decision was received and what was forwarded where.
VARIABLES pforward

vars == <<cvote, calive, cfaulty, cphase, cdecision,
          pvote, palive, pdecision, pforward>>

TypeInvNB ==
  /\ cvote \in {yes, no, undecided}
  /\ calive \in BOOLEAN
  /\ cfaulty \in BOOLEAN
  /\ cphase \in {waiting, commit, abort}
  /\ cdecision \in {commit, abort, undecided}
  /\ pvote \in [participants -> {yes, no, undecided}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {commit, abort, undecided}]
  /\ pforward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ cvote = undecided
  /\ calive = TRUE
  /\ cfaulty = FALSE
  /\ cphase = waiting
  /\ cdecision = undecided
  /\ pvote = [p \in participants |-> undecided]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pforward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator: send the prepare request to participants.
Request ==
  /\ calive
  /\ cphase = waiting
  /\ cphase' = commit
  /\ UNCHANGED <<cvote, calive, cfaulty, cdecision,
                pvote, palive, pdecision, pforward>>

\* A participant sends its vote to the coordinator.
SendVote(p) ==
  /\ palive[p]
  /\ pvote[p] = undecided
  /\ pvote' = [pvote EXCEPT ![p] = IF \E q \in participants : pvote[q] = no THEN no ELSE yes]
  /\ UNCHANGED <<cvote, calive, cfaulty, cphase, cdecision,
                palive, pdecision, pforward>>

\* Coordinator collects a no vote and aborts instantly.
AbortOnVote ==
  /\ calive
  /\ cphase = commit
  /\ \E p \in participants : pvote[p] = no
  /\ cphase' = abort
  /\ cdecision' = abort
  /\ UNCHANGED <<cvote, calive, cfaulty,
                pvote, palive, pdecision, pforward>>

\* Coordinator times out waiting for votes and aborts.
AbortOnTimeout ==
  /\ calive
  /\ cphase = commit
  /\ \A p \in participants : pvote[p] # undecided
  /\ cphase' = abort
  /\ cdecision' = abort
  /\ UNCHANGED <<cvote, calive, cfaulty,
                pvote, palive, pdecision, pforward>>

\* Coordinator crashes silently while broadcasting.
DetectFault ==
  /\ calive
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<cvote, cphase, cdecision,
                pvote, palive, pdecision, pforward>>

\* Coordinator makes a commit decision (only reachable from the inherited base).
Decide ==
  /\ calive
  /\ cphase = commit
  /\ cvote = yes
  /\ cphase' = commit
  /\ cdecision' = commit
  /\ UNCHANGED <<cvote, calive, cfaulty,
                pvote, palive, pdecision, pforward>>

\* Coordinator dies (becomes faulty) at any time.
Die ==
  /\ calive
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<cvote, cphase, cdecision, pvote,
                palive, pdecision, pforward>>

\* A participant receives the coordinator's decision (pre-decision).
PreDecideFromCoordinator(p) ==
  /\ palive[p]
  /\ pforward[p][p] = notsent
  /\ cphase = commit
  /\ pforward' = [pforward EXCEPT ![p][p] = cdecision]
  /\ UNCHANGED <<cvote, calive, cfaulty, cphase, cdecision,
                pvote, palive, pdecision>>

\* A participant receives a decision forwarded by another participant.
PreDecideFromForward(p) ==
  /\ palive[p]
  /\ pforward[p][p] = notsent
  /\ \E q \in participants : q # p /\ pforward[q][p] # notsent
  /\ pforward' = [pforward EXCEPT ![p][p] = pforward[q][p]]
  /\ UNCHANGED <<cvote, calive, cfaulty, cphase, cdecision,
                pvote, palive, pdecision>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ palive[p]
  /\ pforward[p][p] # notsent
  /\ pforward[p][q] = notsent
  /\ pforward' = [pforward EXCEPT ![p][q] = pforward[p][p]]
  /\ UNCHANGED <<cvote, calive, cfaulty, cphase, cdecision,
                pvote, palive, pdecision>>

\* A participant finalizes its decision once it has forwarded to all others.
DecideNB(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ pforward[p][p] # notsent
  /\ \A q \in participants \ {p} : pforward[p][q] # notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = pforward[p][p]]
  /\ UNCHANGED <<cvote, calive, cfaulty, cphase, cdecision,
                pvote, palive, pforward>>

\* A participant times out and aborts once the coordinator has died and
\* every broadcast and forwarding path is exhausted.
AbortNB(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ ~calive
  /\ ~(\E q \in participants : cphase = commit /\ cvote = yes /\ pforward[q][p] # notsent)
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<cvote, calive, cfaulty, cphase, cdecision,
                pvote, palive, pforward>>

\* A participant crashes and becomes faulty.
CrashNB(p) ==
  /\ palive[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<cvote, calive, cfaulty, cphase, cdecision,
                pvote, pdecision, pforward>>

\* Coordinator progress (excluding death) is strongly fair; participant
\* progress (including forwarding) is weakly fair, which is precisely what
\* the reliable broadcast needs to guarantee termination.
NextNB ==
  \/ Request \/ AbortOnVote \/ AbortOnTimeout \/ Decide
  \/ \E p \in participants : SendVote(p) \/ CrashNB(p) \/ AbortNB(p)
  \/ \E p, q \in participants : q # p /\ Forward(p, q)
  \/ \E p \in participants : PreDecideFromCoordinator(p) \/ PreDecideFromForward(p) \/ DecideNB(p)
  \/ DetectFault \/ Die

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(Request)
  /\ WF_vars(AbortOnVote)
  /\ WF_vars(AbortOnTimeout)
  /\ WF_vars(Decide)
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants : PreDecideFromForward(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : q # p /\ Forward(p, q))
  /\ WF_vars(\E p \in participants : DecideNB(p))
  /\ WF_vars(\E p \in participants : AbortNB(p))
  /\ WF_vars(\E p \in participants : CrashNB(p))

\* Safety: the usual atomic-commit agreement and validity guarantees.
AgreementNB ==
  \A p, q \in participants :
    (pdecision[p] = commit /\ pdecision[q] = abort) => FALSE

CommitValidNB ==
  \A p \in participants : pdecision[p] = commit => (\A q \in participants : pvote[q] = yes)

AbortValidNB ==
  \A p, q \in participants :
    (pdecision[p] = abort => (pvote[q] = no \/ ~palive[q] \/ cfaulty))

IrreversibleNB ==
  \A p \in participants : (pdecision[p] \in {commit, abort}) ~> (pdecision[p] \in {commit, abort})

\* Liveness: the base variant's progress plus the reliable-broadcast guarantee
\* that every non-faulty participant eventually decides.
AllDecideNB == <>(\A p \in participants : pdecision[p] # undecided \/ ~palive[p])
NonBlockingNB == \A p \in participants : (palive[p] ~> (pdecision[p] # undecided))

\* Exported name: the specification, the invariant, and the liveness property.
PROPERTIES == AllDecideNB /\ NonBlockingNB /\ AgreementNB /\ CommitValidNB /\ AbortValidNB /\ IrreversibleNB
INVARIANTS == TypeInvNB

====