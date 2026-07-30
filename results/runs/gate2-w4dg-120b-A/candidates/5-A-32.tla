---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decided, faulty, sentVote, requestSent, rxVote, rxDecision, decision, coordAlive, coordFaulty

vars == <<vote, alive, decided, faulty, sentVote, requestSent, rxVote, rxDecision, decision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requestSent \in [participants -> BOOLEAN]
  /\ rxVote \in [participants -> {yes, no, waiting}]
  /\ rxDecision \in [participants -> {commit, abort, notsent}]
  /\ decision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decided = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ requestSent = [p \in participants |-> FALSE]
  /\ rxVote = [p \in participants |-> waiting]
  /\ rxDecision = [p \in participants |-> notsent]
  /\ decision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendRequest(p) ==
  /\ coordAlive
  /\ ~requestSent[p]
  /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, rxVote, rxDecision, decision, coordAlive, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ decision = undecided
  /\ requestSent[p]
  /\ rxVote[p] = waiting
  /\ sentVote[p]
  /\ rxVote' = [rxVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requestSent, rxDecision, decision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ decision = undecided
  /\ requestSent[p]
  /\ rxVote[p] = waiting
  /\ ~alive[p]
  /\ decision' = abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requestSent, rxVote, rxDecision, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ decision = undecided
  /\ \A p \in participants : requestSent[p] /\ rxVote[p] # waiting
  /\ decision' = IF \A p \in participants : rxVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requestSent, rxVote, rxDecision, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ decision \in {commit, abort}
  /\ rxDecision[p] = notsent
  /\ rxDecision' = [rxDecision EXCEPT ![p] = decision]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requestSent, rxVote, decision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requestSent, rxVote, rxDecision, decision>>

SendVote(p) ==
  /\ alive[p]
  /\ requestSent[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, requestSent, rxVote, rxDecision, decision, coordAlive, coordFaulty>>

AbortOnNo(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requestSent, rxVote, rxDecision, decision, coordAlive, coordFaulty>>

AbortOnNoRequest(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~coordAlive
  /\ ~requestSent[p]
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requestSent, rxVote, rxDecision, decision, coordAlive, coordFaulty>>

DecideByBroadcast(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ rxDecision[p] # notsent
  /\ decided' = [decided EXCEPT ![p] = rxDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requestSent, rxVote, rxDecision, decision, coordAlive, coordFaulty>>

Crash(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decided, sentVote, requestSent, rxVote, rxDecision, decision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendRequest(p) \/ RecvVote(p) \/ DetectFault(p) \/ Broadcast(p)
  \/ \E p \in participants : SendVote(p) \/ AbortOnNo(p) \/ AbortOnNoRequest(p) \/ DecideByBroadcast(p) \/ Crash(p)
  \/ MakeDecision
  \/ CoordDie

Spec == Init /\ [][Next]_vars

DecisionAgreed ==
  \A p1, p2 \in participants :
    (decided[p1] = commit /\ decided[p2] = abort) => FALSE

CommitOnlyWithAllYes ==
  (\E p \in participants : decided[p] = commit) => (\A p \in participants : vote[p] = yes)

AbortOnlyWithNoOrFault ==
  (\E p \in participants : decided[p] = abort) => ( (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ coordFaulty)

Irreversible ==
  \A p \in participants : (decided[p] = commit) ~> (decided[p] = commit) /\ (decided[p] = abort) ~> (decided[p] = abort)

DecisionEventuallyMade ==
  <>(\A p \in participants : decided[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

====