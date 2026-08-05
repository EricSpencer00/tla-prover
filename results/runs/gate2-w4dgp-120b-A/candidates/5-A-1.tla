---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentreq, votefrom, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentreq, votefrom, broadcasted, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentreq \in [participants -> BOOLEAN]
  /\ votefrom \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentreq = [p \in participants |-> FALSE]
  /\ votefrom = [p \in participants |-> waiting]
  /\ broadcasted = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendReq(p) ==
  /\ coordAlive
  /\ ~ sentreq[p]
  /\ sentreq' = [sentreq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, votefrom, broadcasted, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ sentreq[p]
  /\ votefrom[p] = waiting
  /\ alive[p]
  /\ votefrom' = [votefrom EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentreq, broadcasted, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ sentreq[p]
  /\ votefrom[p] = waiting
  /\ ~ alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentreq, votefrom, broadcasted, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : sentreq[p]
  /\ coordDecision' = (IF \A p \in participants : vote[p] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<vote, alive, decision, faulty, sentreq, votefrom, broadcasted, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcasted[p] = notsent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentreq, votefrom, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentreq, votefrom, broadcasted, coordDecision>>

SendVote(p) ==
  /\ alive[p]
  /\ sentreq[p]
  /\ ~ sentreq[p]@prime
  /\ UNCHANGED <<vote, alive, decision, faulty, sentreq, votefrom, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentreq[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentreq, votefrom, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~ sentreq[p]
  /\ ~ coordAlive
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentreq, votefrom, broadcasted, coordDecision, coordAlive, coordFaulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcasted[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentreq, votefrom, broadcasted, coordDecision, coordAlive, coordFaulty>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentreq, votefrom, broadcasted, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants :
        SendReq(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ Decide(p) \/ Die(p)
  \/ MakeDecision
  \/ CoordDie

Spec == Init /\ [][Next]_vars
          /\ WF_vars(\E p \in participants : SendReq(p))
          /\ WF_vars(\E p \in participants : ReceiveVote(p))
          /\ WF_vars(\E p \in participants : DetectFault(p))
          /\ WF_vars(MakeDecision)
          /\ WF_vars(\E p \in participants : Broadcast(p))
          /\ WF_vars(\E p \in participants : SendVote(p))
          /\ WF_vars(\E p \in participants : AbortOnVote(p))
          /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
          /\ WF_vars(\E p \in participants : Decide(p))

Agreement ==
  \A p1, p2 \in participants :
    ~(decision[p1] = commit /\ decision[p2] = abort)

CommitValidity ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity ==
  \A p \in participants :
    decision[p] = abort =>
      (\E q \in participants : vote[q] = no \/ faulty[q] \/ coordFaulty)

Irrevocability ==
  \A p \in participants :
    /\ (decision[p] = commit => decision[p] = commit @prime)
    /\ (decision[p] = abort => decision[p] = abort @prime)

AC3Live == <>(\A p \in participants : decision[p] # undecided \/ (\E p \in participants : faulty[p]) \/ coordFaulty)

====