---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

N1 == Node
I1 == initiator
R1 == R

VARIABLES parent, sent, acked, active

vars == <<parent, sent, acked, active>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ sent \in SUBSET R
  /\ acked \in SUBSET R
  /\ active \in [Node -> BOOLEAN]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ sent = {}
  /\ acked = {}
  /\ active = [n \in Node |-> TRUE]

StartEcho(n) ==
  /\ parent[n] = NoNode
  /\ \A p \in Node : parent[p] # n
  /\ parent' = [parent EXCEPT ![n] = initiator]
  /\ UNCHANGED <<sent, acked, active>>

Send(m) ==
  /\ m \notin sent
  /\ sent' = sent \cup {m}
  /\ UNCHANGED <<parent, acked, active>>

Ack(m) ==
  /\ m \in sent
  /\ m \notin acked
  /\ acked' = acked \cup {m}
  /\ UNCHANGED <<parent, sent, active>>

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<parent, sent, acked>>

Next ==
  \/ \E n \in Node : StartEcho(n)
  \/ \E m \in R : Send(m)
  \/ \E m \in R : Ack(m)
  \/ \E n \in Node : Deactivate(n)

AncestorProperties ==
  /\ initiator \in {n \in Node : parent[n] # NoNode}
  /\ \A a, b \in Node :
       (parent[a] = b /\ parent[b] # NoNode) => parent[a] # a

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Node : StartEcho(n))

TestSpec == Spec

====