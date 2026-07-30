---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-Blocking Atomic Commitment Protocol with reliable broadcast
\* (forwarding pre-decisions between participants). Participants forward
\* decisions before delivering locally, so a coordinator crash cannot
\* block termination of the non-faulty participants.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, vsent,
          req, cvote, broadcast, cdecision, calive, cfaulty,
          forward

vars == << pvote, palive, pdecision, pfaulty, vsent,
           req, cvote, broadcast, cdecision, calive, cfaulty,
           forward >>

\* forward[i][j] is participant i's record of what it has sent to j:
\* notsent/commit/abort (the pre-decision forwarded to j). The i-th entry
\* of its own table is the pre-decision i has received (or stores it
\* locally before forwarding).
Todos == Cardinality(participants)
Stages == {notsent, commit, abort}

TypeInvNB ==
  /\ pvote \in [participants -> {yes, no, undecided}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ vsent \in [participants -> BOOLEAN]
  /\ req \in {waiting, yes, no}
  /\ cvote \in {undecided, yes, no}
  /\ broadcast \in [participants -> {undecided, commit, abort}]
  /\ cdecision \in {undecided, commit, abort}
  /\ calive \in BOOLEAN
  /\ cfaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> Stages]]

\* Every participant starts with an empty forwarding table.
InitNB ==
  /\ pvote = [p \in participants |-> undecided]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ vsent = [p \in participants |-> FALSE]
  /\ req = waiting
  /\ cvote = undecided
  /\ broadcast = [p \in participants |-> undecided]
  /\ cdecision = undecided
  /\ calive = TRUE
  /\ cfaulty = FALSE
  /\ forward = [i \in participants |-> [j \in participants |-> notsent]]

SendVote(p) ==
  /\ calive
  /\ p \in participants
  /\ palive[p]
  /\ ~vsent[p]
  /\ pvote[p] = undecided
  /\ \E v \in {yes, no} : pvote' = [pvote EXCEPT ![p] = v]
  /\ vsent' = [vsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << palive, pdecision, pfaulty,
                  req, cvote, broadcast, cdecision,
                  calive, cfaulty, forward >>

SendRequest ==
  /\ calive
  /\ req = waiting
  /\ \E v \in {yes, no} : req' = v
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, cvote, broadcast, cdecision,
                  calive, cfaulty, forward >>

GetVote ==
  /\ calive
  /\ req \in {yes, no}
  /\ cvote = undecided
  /\ \E p \in participants : pvote[p] \in {yes, no}
  /\ LET v == CHOOSE w \in {yes, no} :
                  \E p \in participants : pvote[p] = w
     IN cvote' = v
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, req, broadcast, cdecision,
                  calive, cfaulty, forward >>

DetectFault ==
  /\ calive
  /\ cvote = undecided
  /\ \E p \in participants : pvote[p] = no
  /\ cvote' = no
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, req, broadcast, cdecision,
                  calive, cfaulty, forward >>

MakeDecision ==
  /\ calive
  /\ cvote \in {yes, no}
  /\ cdecision = undecided
  /\ cdecision' = IF cvote = yes THEN commit ELSE abort
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, req, cvote, broadcast,
                  calive, cfaulty, forward >>

Broadcast(p) ==
  /\ calive
  /\ cdecision \in {commit, abort}
  /\ broadcast[p] = undecided
  /\ broadcast' = [broadcast EXCEPT ![p] = cdecision]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, req, cvote, cdecision,
                  calive, cfaulty, forward >>

PreDecide(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ pvote[p] = yes
  /\ broadcast[p] # notsent
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = broadcast[p]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, req, cvote, broadcast, cdecision,
                  calive, cfaulty >>

PreDecideFrom(i, p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ forward[i][p] \in {commit, abort}
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = forward[i][p]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, req, cvote, broadcast, cdecision,
                  calive, cfaulty >>

Forward(p, q) ==
  /\ palive[p]
  /\ forward[p][p] \in {commit, abort}
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, req, cvote, broadcast, cdecision,
                  calive, cfaulty >>

Decide(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ \A q \in participants : forward[p][q] \in {commit, abort}
  /\ pdecision' = [pdecision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED << pvote, palive, pfaulty,
                  vsent, req, cvote, broadcast, cdecision,
                  calive, cfaulty, forward >>

AbortOnTimeout(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ ~calive
  /\ (\A q \in participants : broadcast[q] = notsent)
  /\ (\A i \in participants, q \in participants :
        ~palive[i] => forward[i][q] = notsent)
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED << pvote, palive, pfaulty,
                  vsent, req, cvote, broadcast, cdecision,
                  calive, cfaulty, forward >>

Die(p) ==
  /\ palive[p]
  /\ ~pfaulty[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pvote, pdecision, vsent, req,
                  cvote, broadcast, cdecision, calive,
                  cfaulty, forward >>

DieCoord ==
  /\ calive
  /\ ~cfaulty
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty,
                  vsent, req, cvote, broadcast,
                  cdecision, forward >>

NextNB ==
  \/ SendRequest \/ GetVote \/ DetectFault
  \/ MakeDecision \/ DieCoord
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : Broadcast(p)
  \/ \E p \in participants : PreDecide(p)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : Die(p)
  \/ \E p \in participants, q \in participants : PreDecideFrom(p, q)
  \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB == InitNB /\ [][NextNB]_vars

\* No two participants ever disagree on the final outcome.
Agreement ==
  \A i \in participants, j \in participants :
    (pdecision[i] = commit /\ pdecision[j] = abort) => FALSE

\* A commit only follows a unanimous yes-vote.
AllYes =>
  \A i \in participants : pvote[i] = yes
CommitValidity == \A p \in participants : pdecision[p] = commit => AllYes

AnyAbort =>
  \/ \E x \in participants : pvote[x] = no
  \/ \E x \in participants : pfaulty[x]
  \/ cfaulty
AbortValidity == \A p \in participants : pdecision[p] = abort => AnyAbort

\* Decisions are irreversible (or permanently undecided if never reached).
Irreversible ==
  \A p \in participants :
    pdecision[p] \in {commit, abort} =>
      (pdecision[p] = commit \/ pdecision[p] = abort)

\* Either all participants decide, or some participant or the coordinator is
\* known to be faulty.
Terminating == <>(\A p \in participants : pdecision[p] \in {commit, abort})
                \/ (\E p \in participants : pfaulty[p])
                \/ cfaulty

\* Every non-faulty participant eventually decides -- guaranteed by
\* reliable broadcast forwarding, not satisfied by the simple broadcast.
DecideEventually ==
  \A p \in participants :
    TRUE ~> (pdecision[p] = commit \/ pdecision[p] = abort)

PostRecv(p) ==
  (broadcast[p] \in {commit, abort} \/ forward[p][p] \in {commit, abort})
  ~> pdecision[p] \in {commit, abort}
ProgressNB == PostRecv(coord)

====