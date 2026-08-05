---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, recvVote, sentDecision

vars == <<vote, alive, decision, faulty, sentVote, recvVote, sentDecision>>

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]

CoordSendReq(p) ==
  /\ alive["coord"]
  /\ sentVote[p] = FALSE
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, recvVote, sentDecision>>

CoordRecvVote(p) ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ \A q \in participants : sentVote[q]
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, sentDecision>>

CoordDetectFault(p) ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ \A q \in participants : sentVote[q]
  /\ recvVote[p] = waiting
  /\ alive[p] = FALSE
  /\ decision' = [decision EXCEPT !["coord"] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, recvVote, sentDecision>>

CoordDecide ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ \A p \in participants : recvVote[p] # waiting
  /\ decision' = [decision EXCEPT !["coord"] =
        (IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort)]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, recvVote, sentDecision>>

CoordBroadcast(p) ==
  /\ alive["coord"]
  /\ decision["coord"] # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = decision["coord"]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, recvVote>>

CoordDie ==
  /\ alive["coord"]
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, recvVote, sentDecision>>

PartSendVote(p) ==
  /\ alive[p]
  /\ sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, alive, decision, faulty, recvVote, sentDecision>>

PartAbort ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = undecided
       /\ sentVote[p] = FALSE
       /\ vote[p] = no
       /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, recvVote, sentDecision>>

PartAbortOnNoReq(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p] = FALSE
  /\ alive["coord"] = FALSE
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, recvVote, sentDecision>>

PartDecide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, recvVote, sentDecision>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, recvVote, sentDecision>>

PartProgress ==
  \/ \E p \in participants :
       PartSendVote(p) \/ PartAbortOnNoReq(p) \/ PartDecide(p)
  \/ PartAbort

CoordProgress ==
  \/ \E p \in participants :
       CoordSendReq(p) \/ CoordRecvVote(p) \/ CoordDetectFault(p) \/ CoordBroadcast(p)
  \/ CoordDecide

Next == \/ PartProgress \/ CoordProgress \/ CoordDie \/ PartDie("coord")

Spec == /\ Init
        /\ [][Next]_vars
        /\ SF_vars(CoordProgress)
        /\ SF_vars(PartProgress)

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]

AC1 == \A p1, p2 \in participants :
         ~(decision[p1] = commit /\ decision[p2] = abort)

AC2 == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AC3 == \A p \in participants :
         decision[p] = abort =>
           (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ faulty["coord"]

AC4 == \A p \in participants :
         /\ (decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
         /\ (decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])

AC3Live == <>(\E p \in participants :
                 decision[p] # undecided \/ (\E q \in participants : faulty[q]) \/ faulty["coord"])

====