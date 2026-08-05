---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME yes # no

VARIABLES vote, alive, decision, faulty, voteSent, request, cVote, broadcast, cDecision, cAlive, cFaulty, fwTable

vars == <<vote, alive, decision, faulty, voteSent, request, cVote, broadcast, cDecision, cAlive, cFaulty, fwTable>>

NoFw == [p \in participants |-> notsent]

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ request \in {waiting, notsent}
  /\ cVote \in {yes, no, notsent}
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ cDecision \in {notsent, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN
  /\ fwTable \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ request = waiting
  /\ cVote = notsent
  /\ broadcast = [p \in participants |-> notsent]
  /\ cDecision = notsent
  /\ cAlive = TRUE
  /\ cFaulty = FALSE
  /\ fwTable = [p \in participants |-> NoFw]

SendRequest ==
  /\ request = waiting
  /\ cAlive
  /\ request' = notsent
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, cVote, broadcast, cDecision, cAlive, cFaulty, fwTable>>

GetVote(p) ==
  /\ request = notsent
  /\ voteSent[p] = FALSE
  /\ alive[p]
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, request, cVote, broadcast, cDecision, cAlive, cFaulty, fwTable>>

DetectFault ==
  /\ request = notsent
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, request, cVote, broadcast, cDecision, fwTable>>

MakeDecision(v) ==
  /\ request = notsent
  /\ cAlive
  /\ cVote = notsent
  /\ cVote' = v
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, request, broadcast, cDecision, cAlive, cFaulty, fwTable>>

BroadcastDecision ==
  /\ request = notsent
  /\ cAlive
  /\ cVote # notsent
  /\ cDecision = notsent
  /\ cDecision' = cVote
  /\ broadcast' = [p \in participants |-> cVote]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, request, cVote, cAlive, cFaulty, fwTable>>

Die ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, request, cVote, broadcast, cDecision, fwTable>>

PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, request, cVote, broadcast, cDecision, cAlive, cFaulty, fwTable>>

PreDecideFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants : q # p /\ alive[q] /\ fwTable[q][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in {commit, abort} : \E q \in participants : q # p /\ alive[q] /\ fwTable[q][p] = v]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, request, cVote, broadcast, cDecision, cAlive, cFaulty, fwTable>>

Forward(p, q) ==
  /\ alive[p]
  /\ alive[q]
  /\ p # q
  /\ decision[p] # undecided
  /\ fwTable[p][q] = notsent
  /\ fwTable' = [fwTable EXCEPT ![p][q] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, request, cVote, broadcast, cDecision, cAlive, cFaulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ \A q \in participants : q # p => fwTable[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, request, cVote, broadcast, cDecision, cAlive, cFaulty, fwTable>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~cAlive
  /\ \A q \in participants : broadcast[q] = notsent
  /\ \A q \in participants : faulty[q] => (alive[q] => fwTable[q][p] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, request, cVote, broadcast, cDecision, cAlive, cFaulty, fwTable>>

Next ==
  \/ SendRequest \/ DetectFault \/ Die
  \/ \E p \in participants :
       \/ GetVote(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p) \/ AbortTimeout(p)
       \/ \E q \in participants : Forward(p, q)
  \/ \E v \in {yes, no} : MakeDecision(v)
  \/ BroadcastDecision

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : GetVote(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ AbortTimeout(p))
  /\ SF_vars(\E v \in {yes, no} : MakeDecision(v))
  /\ WF_vars(Die)
  /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
  /\ SF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortTimeout(p))

Agreement ==
  ~ \E p, q \in participants : decision[p] = commit /\ decision[q] = abort

CommitValidity ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity ==
  \E p \in participants : decision[p] = abort =>
    (\E q \in participants : vote[q] = no \/ faulty[q] \/ cFaulty)

Irrevocability ==
  \A p \in participants : (decision[p] = commit \/ decision[p] = abort) => (decision[p] = commit \/ decision[p] = abort)

DecideEventually ==
  \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] = commit \/ decision[p] = abort)

TerminateSomeFault ==
  (\A p \in participants : decision[p] # undecided \/ faulty[p] \/ cFaulty) ~> TRUE

====