---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* An ACP-NB participant's forwarding table is a per-destination decision entry:
\* [ participants -> {notsent, commit, abort} ]
\* The entry at its own index tracks the pre-decision it has received; entries
\* at other indices track which decisions it has already forwarded to them.

VARIABLES partVote, partAlive, partDecision, partFaulty, partSentVote, partTable
VARIABLES coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == << partVote, partAlive, partDecision, partFaulty, partSentVote, partTable,
           coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

TypeOK ==
  /\ partVote \in [ participants -> {yes, no, undecided} ]
  /\ partAlive \subseteq participants
  /\ partDecision \in [ participants -> {commit, abort, undecided} ]
  /\ partFaulty \subseteq participants
  /\ partSentVote \in [ participants -> BOOLEAN ]
  /\ partTable \in [ participants -> [ participants -> {notsent, commit, abort} ] ]
  /\ coordRequest \in {waiting, yes, no, undecided}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in {commit, abort, undecided}
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ partVote = [ p \in participants |-> undecided ]
  /\ partAlive = participants
  /\ partDecision = [ p \in participants |-> undecided ]
  /\ partFaulty = {}
  /\ partSentVote = [ p \in participants |-> FALSE ]
  /\ partTable = [ p \in participants |-> [ q \in participants |-> notsent ] ]
  /\ coordRequest = waiting
  /\ coordVote = undecided
  /\ coordBroadcast = undecided
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* The coordinator collects votes, decides, then broadcasts the same decision
\* to all participants. Its broadcast is one-shot per decision (the base
\* protocol's invariant guarantees it is sent to every participant exactly once).
SendRequest ==
  /\ coordAlive
  /\ coordRequest = waiting
  /\ coordRequest' = undecided
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSentVote, partTable,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

GetVote(p) ==
  /\ coordAlive
  /\ coordRequest \in {yes, no}
  /\ ~ partSentVote[p]
  /\ partVote' = [ partVote EXCEPT ![p] = coordRequest ]
  /\ partSentVote' = [ partSentVote EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << partAlive, partDecision, partFaulty, partTable,
                 coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

DetectFault ==
  /\ coordAlive
  /\ coordVote = undecided
  /\ \E p \in participants : partSentVote[p]
  /\ \E q \in participants : q \notin partAlive
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSentVote, partTable,
                 coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordVote \in {yes, no}
  /\ coordDecision' = coordVote
  /\ UNCHANGED << partVote, partAlive, partDecision partFaulty, partSentVote, partTable,
                 coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty >>

Broadcast ==
  /\ coordAlive
  /\ coordDecision \in {yes, no}
  /\ coordBroadcast = undecided
  /\ coordBroadcast' = coordDecision
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSentVote, partTable,
                 coordRequest, coordVote, coordDecision, coordAlive, coordFaulty >>

Die ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSentVote, partTable,
                 coordRequest, coordVote, coordBroadcast, coordDecision >>

\* A participant adopts the coordinator's broadcast locally.
PreDecideCoord(p) ==
  /\ p \in partAlive
  /\ partDecision[p] = undecided
  /\ coordBroadcast \in {commit, abort}
  /\ partTable[p][p] = notsent
  /\ partTable' = [ partTable EXCEPT ![p][p] = coordBroadcast ]
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSentVote,
                 coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

\* A participant adopts a forwarded decision (the failure case the base protocol
\* cannot handle: the coordinator died mid-broadcast).
PreDecideForward(p) ==
  /\ p \in partAlive
  /\ partDecision[p] = undecided
  /\ partTable[p][p] = notsent
  /\ \E q \in participants : partTable[q][p] \in {commit, abort}
  /\ LET d == CHOOSE q \in participants : partTable[q][p] \in {commit, abort} ![q][p] IN
       partTable' = [ partTable EXCEPT ![p][p] = d ]
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSentVote,
                 coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

\* Only after a participant has forwarded its pre-decision to every other
\* participant may it finalize its own decision -- this forward-before-decide
\* discipline is what guarantees progress even after the coordinator dies.
Forward(p, q) ==
  /\ p \in partAlive
  /\ partTable[p][p] \in {commit, abort}
  /\ partTable[p][q] = notsent
  /\ partTable' = [ partTable EXCEPT ![p][q] = partTable[p][p] ]
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty, partSentVote,
                 coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

Decide(p) ==
  /\ p \in partAlive
  /\ partDecision[p] = undecided
  /\ partTable[p][p] \in {commit, abort}
  /\ \A q \in participants \ {p} : partTable[p][q] = partTable[p][p]
  /\ partDecision' = [ partDecision EXCEPT ![p] = partTable[p][p] ]
  /\ UNCHANGED << partVote, partAlive, partFaulty, partSentVote, partTable,
                 coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

AbortOnTimeout(p) ==
  /\ p \in partAlive
  /\ partDecision[p] = undecided
  /\ ~ coordAlive
  /\ \A q \in participants : coordBroadcast \notin {commit, abort} \/ q \in partAlive
  /\ \A q \in participants : q \notin partAlive => partTable[q][p] = notsent
  /\ partDecision' = [ partDecision EXCEPT ![p] = abort ]
  /\ UNCHANGED << partVote, partAlive, partFaulty, partSentVote, partTable,
                 coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

DieParticipant(p) ==
  /\ p \in partAlive
  /\ partAlive' = partAlive \ {p}
  /\ partFaulty' = partFaulty \cup {p}
  /\ UNCHANGED << partVote, partDecision, partSentVote, partTable,
                 coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

Next ==
  \/ SendRequest \/ DetectFault \/ MakeDecision \/ Broadcast \/ Die
  \/ \E p \in participants : GetVote(p) \/ PreDecideCoord(p) \/ PreDecideForward(p)
                         \/ Decide(p) \/ AbortOnTimeout(p) \/ DieParticipant(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(PreDecideCoord(p)) /\ WF_vars(PreDecideForward(p))
                              /\ WF_vars(Decide(p))
  /\ WF_vars(SendRequest) /\ WF_vars(DetectFault) /\ WF_vars(MakeDecision) /\ WF_vars(Broadcast)

\* AC1: No two participants ever disagree on the final decision.
Agreement == \A p, q \in participants : (partDecision[p] = commit) => (partDecision[q] = commit)

\* AC2: A commit is only possible if every participant voted yes.
CommitValidity == \A p \in participants : partDecision[p] = commit => (\A q \in participants : partVote[q] = yes)

\* AC3: An abort is always rationalizable -- some participant voted no, or some
\* participant is known to be faulty, or the coordinator is known to be faulty.
AbortRationale ==
  \A p \in participants :
    partDecision[p] = abort =>
      \/ \E q \in participants : partVote[q] = no
      \/ partFaulty # {}
      \/ coordFaulty

\* AC4: Once a participant decides, it never flips its decision.
Irreversibility == \A p \in participants : (partDecision[p] = undecided) ~> (partDecision[p] # undecided)

\* AC5: Every non-faulty participant eventually reaches a decision (commit or abort).
Liveness == \A p \in participants : p \in partAlive ~> (partDecision[p] # undecided)

====