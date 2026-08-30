---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast: participants forward decisions to each other BEFORE
\* finalizing locally, so a decision can still reach everyone even if the
\* coordinator dies during broadcast. Crash-fault tolerant action set.

VARIABLES cvote, calive, cdecision, cfaulty, cdecisionSent,
          pdecision, pfaulty, pvoted, pforward

vars == <<cvote, calive, cdecision, cfaulty, cdecisionSent,
           pdecision, pfaulty, pvoted, pforward>>

Init ==
  /\ \E p \in participants : cvote = [p \in participants |-> undecided]
  /\ \E p \in participants : calive = [p \in participants |-> FALSE]
  /\ cdecision = undecided
  /\ cfaulty = FALSE
  /\ cdecisionSent = [p \in participants |-> FALSE]
  /\ \E p \in participants :
        pdecision = [q \in participants |-> [to : p, val : undecided]]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ pvoted = [p \in participants |-> FALSE]
  /\ pforward = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator opens a new transaction round.
SendRequest(p) ==
  /\ ~calive[p]
  /\ \A q \in participants : ~calive[q]
  /\ \A q \in participants : cvote[q] = undecided
  /\ calive' = [calive EXCEPT ![p] = TRUE]
  /\ cvote' = [q \in participants |-> waiting]
  /\ cdecisionSent' = [q \in participants |-> FALSE]
  /\ pdecision' = [r \in participants |-> [to |-> p, val |-> undecided]]
  /\ pforward' = [q \in participants |-> [r \in participants |-> notsent]]
  /\ UNCHANGED <<cdecision, cfaulty, pfaulty, pvoted>>

\* Coordinator collects a vote from one participant.
GetVote(p, v) ==
  /\ calive[p]
  /\ cvote[p] = waiting
  /\ cvote' = [cvote EXCEPT ![p] = v]
  /\ pvoted' = [pvoted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<calive, cdecision, cfaulty, cdecisionSent,
                 pdecision, pfaulty, pforward>>

\* Coordinator crashes silently while at least one other participant is alive.
DetectFault(p) ==
  /\ calive[p]
  /\ \E q \in participants : calive[q]
  /\ calive' = [calive EXCEPT ![p] = FALSE]
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<cvote, cdecision, cdecisionSent,
                 pdecision, pfaulty, pvoted, pforward>>

\* Coordinator makes the decision only once every participant has voted.
MakeDecision(v) ==
  /\ cdecision = undecided
  /\ \A p \in participants : cvote[p] \in {yes, no}
  /\ cdecision' = v
  /\ UNCHANGED <<cvote, calive, cdecisionSent, pfaulty, pvoted, pforward, pdecision>>

Broadcast(p) ==
  /\ cdecision # undecided
  /\ ~cdecisionSent[p]
  /\ calive[p]
  /\ pdecision' = [pdecision EXCEPT ![p] = [to |-> p, val |-> cdecision]]
  /\ cdecisionSent' = [cdecisionSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<cvote, calive, cdecision, cfaulty, pfaulty, pvoted, pforward>>

\* A participant adopts the coordinator's pre-decision, storing it locally.
PreDecideFromCoord(p) ==
  /\ ~pfaulty[p]
  /\ pdecision[p].val # undecided
  /\ pdecision[p].to = p
  /\ pdecision[p].val # notsent
  /\ pforward[p][p] = notsent
  /\ pforward' = [pforward EXCEPT ![p][p] = pdecision[p].val]
  /\ UNCHANGED <<cvote, calive, cdecision, cfaulty,
                 cdecisionSent, pdecision, pfaulty, pvoted>>

\* A participant adopts a pre-decision forwarded by another participant.
PreDecideFromForward(p) ==
  /\ ~pfaulty[p]
  /\ pdecision[p].val = undecided
  /\ \E q \in participants :
        /\ pforward[q][p] # notsent
        /\ pdecision' = [pdecision EXCEPT ![p] = [to |-> p, val |-> pforward[q][p]]]
  /\ UNCHANGED <<cvote, calive, cdecision, cfaulty,
                 cdecisionSent, pfaulty, pvoted, pforward>>

\* A participant forwards its cached pre-decision to another participant.
Forward(p, o) ==
  /\ ~pfaulty[p]
  /\ pforward[p][p] # notsent
  /\ pforward[p][o] = notsent
  /\ pforward' = [pforward EXCEPT ![p][o] = pforward[p][p]]
  /\ UNCHANGED <<cvote, calive, cdecision, cfaulty,
                 cdecisionSent, pdecision, pfaulty, pvoted>>

\* The participant finalizes only after forwarding its pre-decision to everyone.
Decide(p) ==
  /\ ~pfaulty[p]
  /\ pforward[p][p] # notsent
  /\ \A q \in participants : pforward[p][q] # notsent
  /\ pdecision[p].val = notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = [to |-> p, val |-> pforward[p][p]]]
  /\ UNCHANGED <<cvote, calive, cdecision, cfaulty,
                 cdecisionSent, pfaulty, pvoted, pforward>>

AbortOnTimeout(p) ==
  /\ ~pfaulty[p]
  /\ pdecision[p].val = undecided
  /\ cfaulty
  /\ \A q \in participants : ~cdecisionSent[q]
  /\ \A q \in participants : pfaulty[q] => pforward[q][p] = notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = [to |-> p, val |-> abort]]
  /\ UNCHANGED <<cvote, calive, cdecision, cfaulty,
                 cdecisionSent, pfaulty, pvoted, pforward>>

Die(p) ==
  /\ ~pfaulty[p]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<cvote, calive, cdecision, cfaulty,
                 cdecisionSent, pdecision, pvoted, pforward>>

Next ==
  \/ \E p \in participants : SendRequest(p) \/ DetectFault(p) \/ Broadcast(p)
                          \/ PreDecideFromCoord(p) \/ PreDecideFromForward(p)
                          \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p \in participants, v \in {yes, no} : GetVote(p, v)
  \/ \E p \in participants, o \in participants : Forward(p, o)
  \/ \E v \in {commit, abort} : MakeDecision(v)

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromForward(p))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ SF_vars(\E p \in participants : AbortOnTimeout(p))

TypeInvNB ==
  /\ cvote \in [participants -> {undecided, waiting, yes, no}]
  /\ calive \in [participants -> BOOLEAN]
  /\ cdecision \in {undecided, commit, abort}
  /\ cfaulty \in BOOLEAN
  /\ cdecisionSent \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> [to : participants, val : {undecided, commit, abort}]]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ pvoted \in [participants -> BOOLEAN]
  /\ pforward \in [participants -> [participants -> {notsent, commit, abort}]]

\* Safety: no two participants ever reach different decisions.
AC1 ==
  \A p1, p2 \in participants :
    (pdecision[p1].val = commit /\ pdecision[p2].val = abort) => FALSE

\* Commit is only possible if every vote was yes.
AC2 ==
  ( \E p \in participants : pdecision[p].val = commit ) =>
    (\A q \in participants : cvote[q] = yes)

\* Abort is only possible if some vote was no or some node crashed.
AC3 ==
  ( \E p \in participants : pdecision[p].val = abort ) =>
    \E q \in participants : (cvote[q] = no) \/ pfaulty[q] \/ cfaulty

\* A decision, once made, is permanent.
AC4 ==
  \A p \in participants :
    (pdecision[p].val \in {commit, abort}) ~> (pdecision[p].val \in {commit, abort})

\* Liveness: every non-faulty participant eventually reaches a decision.
AC5 ==
  \A p \in participants :
    (~pfaulty[p]) ~> (pdecision[p].val \in {commit, abort})

====