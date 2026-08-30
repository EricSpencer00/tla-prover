---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, pvoteSent, cred, cvote, cdecision, calive, cfaulty

Vars == <<pvote, palive, pdecision, pfaulty, pvoteSent, cred, cvote, cdecision, calive, cfaulty>>

\* cred is the forwarding table: cred[i][j] is i's forwarding status for j.
\* A participant only decides once it has forwarded its pre-decision to everyone.
CredState == {notsent, commit, abort}

TypeOK ==
  /\ pvote \in [participants -> {yes, no, undecided}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {commit, abort, undecided}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ pvoteSent \in [participants -> BOOLEAN]
  /\ cred \in [participants -> [participants -> CredState]]
  /\ cred[CHOOSE i \in participants : TRUE][CHOOSE i \in participants : TRUE] \in {commit, abort}
  /\ cvote \in {yes, no, undecided}
  /\ cdecision \in {commit, abort, undecided}
  /\ calive \in BOOLEAN
  /\ cfaulty \in BOOLEAN

Init ==
  /\ pvote = [i \in participants |-> undecided]
  /\ palive = [i \in participants |-> TRUE]
  /\ pdecision = [i \in participants |-> undecided]
  /\ pfaulty = [i \in participants |-> FALSE]
  /\ pvoteSent = [i \in participants |-> FALSE]
  /\ cred = [i \in participants |-> [j \in participants |-> notsent]]
  /\ cvote = undecided
  /\ cdecision = undecided
  /\ calive = TRUE
  /\ cfaulty = FALSE

\* Coordinator collects votes and decides (the shared decision is broadcast).
SendRequest ==
  /\ calive
  /\ cvote = undecided
  /\ cvote' = waiting
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cred, cdecision, calive, cfaulty>>

GetVote(i) ==
  /\ cvote = waiting
  /\ pvote[i] \in {yes, no}
  /\ pvoteSent[i]
  /\ cvote' = pvote[i]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cred, cdecision, calive, cfaulty>>

DetectFault(i) ==
  /\ cvote = waiting
  /\ pvote[i] = undecided
  /\ ~pfaulty[i]
  /\ pfaulty' = [pfaulty EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pvoteSent, cred, cvote, cdecision, calive, cfaulty>>

MakeDecision ==
  /\ cvote \in {yes, no}
  /\ cdecision = undecided
  /\ cdecision' = IF cvote = yes THEN commit ELSE abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cred, cvote, calive, cfaulty>>

Broadcast(i) ==
  /\ cdecision \in {commit, abort}
  /\ calive
  /\ cred[i][i] = notsent
  /\ cred' = [cred EXCEPT ![i][i] = cdecision]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cvote, cdecision, calive, cfaulty>>

DieC ==
  /\ calive
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cred, cvote, cdecision>>

\* A participant broadcasts its own vote to the coordinator.
SendVote(i) ==
  /\ pvote[i] = undecided
  /\ ~pvoteSent[i]
  /\ ~pfaulty[i]
  /\ \E v \in {yes, no} : pvote' = [pvote EXCEPT ![i] = v]
  /\ pvoteSent' = [pvoteSent EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<palive, pdecision, pfaulty, cred, cvote, cdecision, calive, cfaulty>>

AbortOnVote(i) ==
  /\ pvote[i] = no
  /\ pdecision[i] = undecided
  /\	pdecision' = [pdecision EXCEPT ![i] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, pvoteSent, cred, cvote, cdecision, calive, cfaulty>>

\* A participant adopts the coordinator's broadcast before deciding.
PreDecideFromCoord(i) ==
  /\ palive[i]
  /\ cred[i][i] = notsent
  /\ cred[i][i] # notsent
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cred, cvote, cdecision, calive, cfaulty>>

\* A participant adopts a forwarded decision before deciding.
PreDecideFromForward(i) ==
  /\ palive[i]
  /\ cred[i][i] = notsent
  /\ \E j \in participants : cred[j][i] # notsent
  /\ cred' = [cred EXCEPT ![i][i] = cred[j][i]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cvote, cdecision, calive, cfaulty>>

ForwardDec(j, i) ==
  /\ palive[j]
  /\ cred[j][j] # notsent
  /\ cred[j][i] = notsent
  /\ cred' = [cred EXCEPT ![j][i] = cred[j][j]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cvote, cdecision, calive, cfaulty>>

\* A participant only finalizes after forwarding to everyone else.
Decide(i) ==
  /\ palive[i]
  /\ pdecision[i] = undecided
  /\ cred[i][i] # notsent
  /\ \A j \in participants : cred[i][j] # notsent
  /\ pdecision' = [pdecision EXCEPT ![i] = cred[i][i]]
  /\ UNCHANGED <<pvote, palive, pfaulty, pvoteSent, cred, cvote, cdecision, calive, cfaulty>>

AbortOnTimeout(i) ==
  /\ palive[i]
  /\ pdecision[i] = undecided
  /\ ~calive
  /\ \A k \in participants : cred[k][i] = notsent
  /\ \A j \in participants : pfaulty[j]
  /\ pdecision' = [pdecision EXCEPT ![i] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, pvoteSent, cred, cvote, cdecision, calive, cfaulty>>

DieP(i) ==
  /\ palive[i]
  /\ palive' = [palive EXCEPT ![i] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, pvoteSent, cred, cvote, cdecision, calive, cfaulty>>

Next ==
  \/ SendRequest \/ MakeDecision \/ DieC
  \/ \E i \in participants :
       \/ GetVote(i) \/ DetectFault(i) \/ Broadcast(i) \/ SendVote(i)
       \/ AbortOnVote(i) \/ PreDecideFromCoord(i) \/ PreDecideFromForward(i)
       \/ Decide(i) \/ AbortOnTimeout(i) \/ DieP(i)
       \/ \E j \in participants : ForwardDec(j, i)

\* Weak fairness on participant progress (voting, pre-deciding, forwarding,
\* deciding, aborting on timeout) and coordinator progress, excluding death.
SpecNB ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A i \in participants :
       /\ WF_Vars(SendVote(i))
       /\ WF_Vars(PreDecideFromCoord(i))
       /\ WF_Vars(PreDecideFromForward(i))
       /\ WF_Vars(\E j \in participants : ForwardDec(j, i))
       /\ WF_Vars(Decide(i))
       /\ WF_Vars(AbortOnTimeout(i))
  /\ WF_Vars(SendRequest) /\ WF_Vars(MakeDecision)

\* Safety: no two participants disagree once decided.
Agreement ==
  \A i, j \in participants : (pdecision[i] = commit /\ pdecision[j] = abort) => FALSE

\* Liveness: every non-faulty participant eventually learns the decision.
EventualDecision ==
  \A i \in participants : (~pfaulty[i]) ~> (pdecision[i] # undecided)

\* Liveness: the protocol always eventually settles or crashes.
EventualDecisionOrFault ==
  <>(\A i \in participants : pdecision[i] # undecided \/ pfaulty[i]) \/ cfaulty

\* Safety: every commit is backed by a unanimous yes vote.
CommitByUnanimousVote ==
  (\E i \in participants : pdecision[i] = commit) => (\A i \in participants : pvote[i] = yes)

\* Safety: an abort is always justified by a no vote or a fault (coordination).
AbortValidity ==
  (\E i \in participants : pdecision[i] = abort) =>
    (\E i \in participants : pvote[i] = no) \/ (\E i \in participants : pfaulty[i]) \/ cfaulty

NoDecisionChange == \A i \in participants : pdecision[i] # undecided ~> (pdecision[i] = pdecision[i])

TypeInvNB == TypeOK

====