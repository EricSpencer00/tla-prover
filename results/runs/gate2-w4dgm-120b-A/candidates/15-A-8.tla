---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

Nodes == 1..N
Echomsg == [snd: Nodes, mtype: {"ECHO"}]

TypeOK ==
  /\ correct \subseteq Nodes
  /\ faulty \subseteq Nodes
  /\ pc \in [Nodes -> {"recvInit", "recvNone", "sentEcho", "accepted"}]
  /\ recv \in [Nodes -> SUBSET Echomsg]
  /\ sent \subseteq Echomsg

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correct) = N - F
  /\ faulty = Nodes \ correct

InitBroadcast ==
  /\ \E x \in Nodes :
        /\ correct = Nodes \ {x}
        /\ faulty = {x}
  /\ \E s \in {"recvInit", "recvNone"} :
        /\ \A p \in Nodes : pc[p] = s
        /\ s = "recvInit"
  /\ recv = [p \in Nodes |-> {}]
  /\ sent = {}

InitRestricted ==
  /\ \E x \in Nodes :
        /\ correct = Nodes \ {x}
        /\ faulty = {x}
  /\ \A p \in Nodes : pc[p] = "recvNone"
  /\ recv = [p \in Nodes |-> {}]
  /\ sent = {}

SafeDeliver(n) ==
  Cardinality({m \in recv[n] : m.mtype = "ECHO"}) >= N - T

AllSentEcho ==
  {m \in sent : m.mtype = "ECHO"}

ReceiveAndAct(n) ==
  /\ n \in correct
  /\ \E newMsgs \in SUBSET AllSentEcho \cup {x \in Nodes : [snd |-> x, mtype |-> "ECHO"]} :
        recv' = [recv EXCEPT ![n] = @ \cup newMsgs]
  /\ pc' = IF pc[n] = "recvNone" /\ pc[n] = "recvInit"
             THEN "recvInit"
             ELSE IF (pc[n] \in {"recvInit", "recvNone"}) /\ Cardinality({m \in recv[n] : m.mtype = "ECHO"}) >= N - 2 * T
                     THEN "sentEcho"
                     ELSE IF pc[n] \in {"recvInit", "recvNone"} /\ Cardinality({m \in recv[n] : m.mtype = "ECHO"}) >= N - T
                     THEN "accepted"
                     ELSE IF pc[n] = "sentEcho" /\ Cardinality({m \in recv[n] : m.mtype = "ECHO"}) >= N - T
                     THEN "accepted"
                     ELSE pc[n]
  /\ sent' = IF pc[n] = "recvInit" /\ pc[n] # "sentEcho" /\ pc[n] # "accepted"
               THEN sent \cup {[snd |-> n, mtype |-> "ECHO"]}
               ELSE IF pc[n] \in {"recvNone", "recvInit"} /\ Cardinality({m \in recv[n] : m.mtype = "ECHO"}) >= N - 2 * T /\ Cardinality({m \in recv[n] : m.mtype = "ECHO"}) < N - T
               THEN sent \cup {[snd |-> n, mtype |-> "ECHO"]}
               ELSE IF pc[n] \in {"recvNone", "recvInit"} /\ Cardinality({m \in recv[n] : m.mtype = "ECHO"}) >= N - T
               THEN sent \cup {[snd |-> n, mtype |-> "ECHO"]}
               ELSE IF pc[n] = "sentEcho" /\ Cardinality({m \in recv[n] : m.mtype = "ECHO"}) >= N - T
               THEN sent \cup {[snd |-> n, mtype |-> "ECHO"]}
               ELSE sent
  /\ UNCHANGED <<correct, faulty>>

Next == \E n \in Nodes : ReceiveAndAct(n)

Spec == InitRestricted /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(ReceiveAndAct(n))

Unforgeable == (\A p \in Nodes : pc[p] \in {"recvNone", "recvNone"}) => (\A p \in Nodes : pc[p] \notin {"sentEcho", "accepted"})
CorrLtl == (\A p \in Nodes : pc[p] = "recvInit") ~> (\A p \in Nodes : pc[p] = "accepted")
RelayLtl == (\E p \in Nodes : pc[p] = "accepted") ~> (\A p \in Nodes : pc[p] = "accepted")

====