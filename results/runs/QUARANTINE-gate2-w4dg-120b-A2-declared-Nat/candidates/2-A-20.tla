---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordSend,
          coordDecision, coordAlive, coordFaulty, forward

vars == <<
  vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordSend,
  coordDecision, coordAlive, coordFaulty, forward
>>

None == "none"

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no}
  /\ coordSend \in [participants -> {yes, no, notsent}]
  /\ coordDecision \in {commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = yes
  /\ coordSend = [p \in participants |-> notsent]
  /\ coordDecision = commit
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest == coordAlive /\ coordReq = waiting /\ coordReq' = yes /\ UNCHANGED vars
GetVote(p) == coordAlive /\ alive[p] /\ coordReq \in {yes, no} /\ ~sentVote[p]
  /\ vote' = [vote EXCEPT ![p] = coordReq]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordReq, coordVote, coordSend,
                 coordDecision, coordAlive, coordFaulty, forward>>
DetectFault == coordAlive /\ coordReq \in {yes, no} /\ \E p \in participants :
  alive[p] /\ vote[p] = undecided /\ coordVote' = vote[p]
MakeDecision == coordAlive /\ coordReq \in {yes, no}
  /\ coordDecision' = IF coordVote = no THEN abort ELSE commit
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                 coordVote, coordSend, faulty, forward>>
Broadcast(p) == coordAlive /\ coordDecision \in {commit, abort} /\ coordSend[p] = notsent
  /\ coordSend' = [coordSend EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
                 coordDecision, coordAlive, coordFaulty, forward>>
Die == coordAlive /\ coordAlive' = FALSE /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
                 coordSend, coordDecision, faulty, forward>>

PreDecideFromCoord(p) ==
  alive[p] /\ decision[p] = undecided /\ coordSend[p] \in {commit, abort}
  /\ forward' = [forward EXCEPT ![p][p] = coordSend[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
                 coordSend, coordDecision, coordAlive, coordFaulty>>
PreDecideFromForward(q, p) ==
  alive[p] /\ decision[p] = undecided /\ forward[q][p] \in {commit, abort}
  /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
                 coordSend, coordDecision, coordAlive, coordFaulty>>
Forward(p, q) ==
  alive[p] /\ forward[p][p] \in {commit, abort} /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
                 coordSend, coordDecision, coordAlive, coordFaulty>>
Decide(p) ==
  alive[p] /\ \A q \in participants : forward[p][q] = forward[p][p]
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote,
                 coordSend, coordDecision, coordAlive, coordFaulty, forward>>
AbortTimeout(p) ==
  alive[p] /\ decision[p] = undecided /\ ~coordAlive
  /\ \A q \in participants : coordSend[q] = notsent
  /\ \A q \in participants : ~faulty[q] => \A r \in participants : forward[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote,
                 coordSend, coordDecision, coordAlive, coordFaulty, forward>>
DieP(p) == alive[p] /\ alive' = [alive EXCEPT ![p] = FALSE] /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coordReq, coordVote, coordSend,
                 coordDecision, coordAlive, coordFaulty, forward>>

NextNB ==
  \/ SendRequest
  \/ DetectFault
  \/ MakeDecision
  \/ Broadcast("none")
  \/ Die
  \/ \E p \in participants :
       GetVote(p) \/ PreDecideFromCoord(p) \/ Decide(p)
       \/ AbortTimeout(p) \/ DieP(p)
       \/ \E q \in participants : PreDecideFromForward(q, p) \/ Forward(p, q)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(GetVote("none"))
  /\ \A p \in participants :
       WF_vars(\E q \in participants : PreDecideFromForward(q, p) \/ Forward(p, q))
       /\ WF_vars(Decide(p))
       /\ WF_vars(SendRequest)
  /\ WF_vars(Die) /\ WF_vars(DieP("none"))
  /\ SF_vars(SendRequest) /\ SF_vars(Decide("none"))

AC1 == \A p \in participants : decision[p] = commit => \A q \in participants : decision[q] = commit
AC2 == (\E p \in participants : decision[p] = commit) => \A q \in participants : vote[q] = yes
AC3 == (\E p \in participants : decision[p] = abort) =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faulty[q]
        \/ coordFaulty
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> decision[p]

AC3Live == <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q] \/ coordFaulty)
AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

Properties == {AC3Live, AC5}

====