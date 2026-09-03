---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Process roles: 0 = correct, 1 = faulty (Byzantine)
\* PC control locations: 0 = init-prefixed, 1 = init-unprefixed, 2 = sent ECHO, 3 = accepted
\* Messages are (sender, type); only ECHO type exists in this model
VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

Nodes == 0..(N - 1)
MsgTypes == {"ech"}
Voters(n) == { m.sender : m \in recv[n] }

TypeOK ==
  /\ correct \subseteq Nodes
  /\ faulty = Nodes \ correct
  /\ Cardinality(faulty) <= T
  /\ pc \in [Nodes -> 0..3]
  /\ recv \in [Nodes -> SUBSET [sender : Nodes, ty : MsgTypes]]
  /\ sent \subseteq [sender : Nodes, ty : MsgTypes]

Init ==
  /\ correct = { n \in Nodes : n >= F }
  /\ faulty = Nodes \ correct
  /\ \A n \in Nodes : pc[n] = IF n < F THEN 1 ELSE 0
  /\ recv = [n \in Nodes |-> {}]
  /\ sent = {}

\* No broadcast at all: every correct process starts without the INIT message
InitNoBcast ==
  /\ Init
  /\ \A n \in correct : pc[n] = 1

Receive(n) ==
  /\ n \in correct
  /\ recv' = [recv EXCEPT ![n] =
        recv[n] \cup (sent \cup { [sender |-> n, ty |-> "ech"] })
          \ { [sender |-> n, ty |-> "ech"] }
      ]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(n) ==
  /\ n \in correct
  /\ pc[n] = 0
  /\ sent' = sent \cup { [sender |-> n, ty |-> "ech"] }
  /\ pc' = [pc EXCEPT ![n] = 2]
  /\ UNCHANGED <<correct, faulty, recv>>

ConditionalEcho(n) ==
  /\ n \in correct
  /\ pc[n] \in 0..1
  /\ Cardinality(Voters(n)) >= N - 2 * T
  /\ Cardinality(Voters(n)) < N - T
  /\ sent' = sent \cup { [sender |-> n, ty |-> "ech"] }
  /\ pc' = [pc EXCEPT ![n] = 2]
  /\ UNCHANGED <<correct, faulty, recv>>

QuorumEcho(n) ==
  /\ n \in correct
  /\ pc[n] \in 0..1
  /\ Cardinality(Voters(n)) >= N - T
  /\ sent' = sent \cup { [sender |-> n, ty |-> "ech"] }
  /\ pc' = [pc EXCEPT ![n] = 3]
  /\ UNCHANGED <<correct, faulty, recv>>

QuorumAccept(n) ==
  /\ n \in correct
  /\ pc[n] = 2
  /\ Cardinality(Voters(n)) >= N - T
  /\ pc' = [pc EXCEPT ![n] = 3]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E n \in Nodes : Receive(n)
  \/ \E n \in Nodes : SendEcho(n)
  \/ \E n \in Nodes : ConditionalEcho(n)
  \/ \E n \in Nodes : QuorumEcho(n)
  \/ \E n \in Nodes : QuorumAccept(n)

Spec == Init /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(Receive(n))
        /\ \A n \in Nodes : WF_vars(SendEcho(n))
        /\ \A n \in Nodes : WF_vars(ConditionalEcho(n))
        /\ \A n \in Nodes : WF_vars(QuorumEcho(n))
        /\ \A n \in Nodes : WF_vars(QuorumAccept(n))

\* No correct participant ever accepts unless the broadcaster actually sent INIT
FCConstraints == \A n \in correct : pc[n] = 3 => pc[n] # 1

\* If everyone got the INIT message, the correct participants all accept eventually
CorrLtl == (\A n \in correct : pc[n] = 0) ~> (\A n \in correct : pc[n] = 3)

RelayLtl == (\E n \in correct : pc[n] = 3) ~> (\A n \in correct : pc[n] = 3)

UnforgLtl == (~(\A n \in correct : pc[n] = 0)) ~> (\A n \in correct : pc[n] # 3)

====