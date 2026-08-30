---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES loc, recv, sentm, correct, faulty

Vars == <<loc, recv, sentm, correct, faulty>>

States == {"initrecv", "initnone", "sentecho", "accepted"}
MsgTypes == {"echo"}
Msgs == [sender : 0 .. (N - 1), typ : MsgTypes]

InitMsgs == {msg \in Msgs : msg.typ = "echo"}

RECURSIVE SumRecv(_)
SumRecv(n) ==
  IF n = 0 THEN 0
  ELSE Cardinality(recv[n - 1]) + SumRecv(n - 1)

InitCorr == CHOOSE K \in [0 .. (N - 1)] -> States :
  \A j \in 0 .. (N - 1) : (j \in K) <=> (j % 2 = 0)

InitNone == CHOOSE K \in [0 .. (N - 1)] -> States :
  \A j \in 0 .. (N - 1) : (j \in K) <=> (j % 2 = 1)

Init ==
  /\ loc = [p \in 0 .. (N - 1) |-> IF p % 2 = 0 THEN "initrecv" ELSE "initnone"]
  /\ recv = [p \in 0 .. (N - 1) |-> {}]
  /\ sentm = {}
  /\ correct = {p \in 0 .. (N - 1) : p % 2 = 0}
  /\ faulty = {p \in 0 .. (N - 1) : p % 2 = 1}

InitAlt ==
  /\ loc = [p \in 0 .. (N - 1) |-> "initnone"]
  /\ recv = [p \in 0 .. (N - 1) |-> {}]
  /\ sentm = {}
  /\ correct = {p \in 0 .. (N - 1) : p % 2 = 0}
  /\ faulty = {p \in 0 .. (N - 1) : p % 2 = 1}

Receive(p, Q) ==
  /\ p \in correct
  /\ loc[p] \in {"initrecv", "initnone"}
  /\ Q \subseteq (sentm \cup InitMsgs)
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup Q]
  /\ UNCHANGED <<sentm, correct, faulty, loc>>

SendEcho(p) ==
  /\ p \in correct
  /\ loc[p] = "initrecv"
  /\ sentm' = sentm \cup {[sender |-> p, typ |-> "echo"]}
  /\ loc' = [loc EXCEPT ![p] = "sentecho"]
  /\ UNCHANGED <<recv, correct, faulty>>

RecvEchoSend(p) ==
  /\ p \in correct
  /\ loc[p] = "initnone"
  /\ (N - 2 * T) <= Cardinality(recv[p])
  /\ Cardinality(recv[p]) < (N - T)
  /\ sentm' = sentm \cup {[sender |-> p, typ |-> "echo"]}
  /\ loc' = [loc EXCEPT ![p] = "sentecho"]
  /\ UNCHANGED <<recv, correct, faulty>>

RecvEchoAccept(p) ==
  /\ p \in correct
  /\ loc[p] = "initnone"
  /\ (N - T) <= Cardinality(recv[p])
  /\ sentm' = sentm \cup {[sender |-> p, typ |-> "echo"]}
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<recv, correct, faulty>>

RelayAccept(p) ==
  /\ p \in correct
  /\ loc[p] = "sentecho"
  /\ (N - T) <= Cardinality(recv[p])
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<recv, sentm, correct, faulty>>

Next ==
  \/ InitAlt
  \/ \E p \in 0 .. (N - 1) : \E Q \in SUBSET InitMsgs : Receive(p, Q)
  \/ \E p \in 0 .. (N - 1) : SendEcho(p)
  \/ \E p \in 0 .. (N - 1) : RecvEchoSend(p)
  \/ \E p \in 0 .. (N - 1) : RecvEchoAccept(p)
  \/ \E p \in 0 .. (N - 1) : RelayAccept(p)

Spec == Init /\ [][Next]_Vars

UnforgLtl == (\A p \in correct : loc[p] = "initrecv") ~> (\A p \in correct : loc[p] = "accepted")

CorrLtl == (\A p \in correct : loc[p] = "initrecv") ~> (\A p \in correct : loc[p] = "accepted")

RelayLtl == (\E p \in correct : loc[p] = "accepted") ~> (\A p \in correct : loc[p] = "accepted")

TypeOK ==
  /\ loc \in [0 .. (N - 1) -> States]
  /\ recv \in [0 .. (N - 1) -> SUBSET MsgTypes]
  /\ sentm \subseteq InitMsgs
  /\ correct \subseteq 0 .. (N - 1)
  /\ faulty \subseteq 0 .. (N - 1)

FCConstraints ==
  /\ correct \cap faulty = {}
  /\ (correct \cup faulty = 0 .. (N - 1))
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

====