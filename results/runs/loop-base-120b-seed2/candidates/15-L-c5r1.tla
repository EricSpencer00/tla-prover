---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, T, F

\* ---------- Process universe ----------
Proc == 1 .. N

\* ---------- Message definition ----------
ECHO == "ECHO"
AllMsgs == { <<p, ECHO>> : p \in Proc }
EchoMsg(p) == <<p, ECHO>>

\* ---------- Variables ----------
VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

\* ---------- Helper definitions ----------
SentEchoSet == { p \in Correct : EchoMsg(p) \in sent }

DistSenders(p) == { m[1] : m \in recv[p] }

EchoCount(p) == Cardinality(DistSenders(p))

\* ---------- Initial state ----------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"InitRecv", "InitNotRecv", "EchoSent", "Accepted"}]
  /\ recv = [p \in Proc |-> {}]
  /\ sent = {}

\* ---------- Actions ----------
Receive(p) ==
  /\ p \in Correct
  /\ \E new \in SUBSET (AllMsgs \ recv[p]) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

InitRecvAccept(p) ==
  /\ pc[p] = "InitRecv"
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoOnly(p) ==
  /\ p \in Correct
  /\ EchoMsg(p) \notin sent
  /\ EchoCount(p) >= N - 2 * T
  /\ EchoCount(p) < N - T
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ EchoMsg(p) \notin sent
  /\ EchoCount(p) >= N - T
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptOnly(p) ==
  /\ p \in Correct
  /\ EchoMsg(p) \in sent
  /\ EchoCount(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv, sent>>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : InitRecvAccept(p)
  \/ \E p \in Correct : SendEchoOnly(p)
  \/ \E p \in Correct : SendEchoAndAccept(p)
  \/ \E p \in Correct : AcceptOnly(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Type invariant ----------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ pc \in [Proc -> {"InitRecv", "InitNotRecv", "EchoSent", "Accepted"}]
  /\ recv \in [Proc -> SUBSET AllMsgs]
  /\ sent \subseteq AllMsgs

\* ---------- Faulty constraints ----------
FCConstraints == sent \subseteq { EchoMsg(p) : p \in Correct }

\* ---------- Liveness properties ----------
CorrLtl ==
  ( \A p \in Correct : pc[p] = "InitRecv" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl ==
  ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

\* ---------- Safety (unforgeability) ----------
UnforgLtl ==
  ( \A p \in Correct : pc[p] = "InitNotRecv" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

====