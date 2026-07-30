---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decided, faulty, sentVote, reqSent, recvVote, sentDecision,
          coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decided, faulty, sentVote, reqSent, recvVote,
          sentDecision, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ reqSent \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decided = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ reqSent = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendReq(p) ==
  /\ coordAlive
  /\ ~reqSent[p]
  /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, recvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSent[p]
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, reqSent,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSent[p]
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, reqSent,
                recvVote, sentDecision, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : recvVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, reqSent,
                recvVote, sentDecision, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, reqSent,
                recvVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, reqSent,
                recvVote, sentDecision, coordDecision, coordFaulty>>

SendVote(p) ==
  /\ alive[p]
  /\ reqSent[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, reqSent, recvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~reqSent[p]
  /\ ~coordAlive
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

DecideOnDecision(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentDecision[p] \in {commit, abort}
  /\ decided' = [decided EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, recvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decided, sentVote, reqSent, recvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendReq(p) \/ ReceiveVote(p) \/ DetectFault(p)
                            \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p)
                            \/ AbortOnTimeout(p) \/ DecideOnDecision(p) \/ Die(p)
  \/ MakeDecision \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendReq(p))
  /\ WF_vars(\E p \in participants : ReceiveVote(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : DecideOnDecision(p))

AC1 == \A p1, p2 \in participants : (decided[p1] = commit /\ decided[p2] = abort) => FALSE

AC2 == \E p \in participants : decided[p] = commit => (\A q \in participants : vote[q] = yes)

AC3 == \E p \in participants : decided[p] = abort =>
        (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ coordFaulty

CommitMonotone ==
  \A p \in participants : (decided[p] = commit) ~> (decided[p] = commit)

AbortMonotone ==
  \A p \in participants : (decided[p] = abort) ~> (decided[p] = abort)

AC4 == CommitMonotone /\ AbortMonotone

DecideSome == \E p \in participants : decided[p] \in {commit, abort}

AC3Liveness == DecideSome \/ (\E p \in participants : faulty[p]) \/ coordFaulty

====