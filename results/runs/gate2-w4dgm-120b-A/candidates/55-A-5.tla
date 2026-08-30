---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node

VARIABLES parent, sent, acked, pending
vars == <<parent, sent, acked, pending>>

Parents == Node \cup {NoNode}
Edges == {e \in Node \times Node : e[1] # e[2]}
INIT ==
  /\ parent = [n \in Node |-> NoNode]
  /\ sent = {}
  /\ acked = {}
  /\ pending = {}

RECURSIVE Ancestors(_)
Ancestors(n) ==
  IF parent[n] = NoNode THEN {}
  ELSE {parent[n]} \cup Ancestors(parent[n])

Start(n, m) ==
  /\ n = initiator
  /\ parent[m] = NoNode
  /\ <<m, n>> \notin sent
  /\ sent' = sent \cup {<<m, n>>}
  /\ UNCHANGED <<parent, acked, pending>>

SendAck(m, n) ==
  /\ <<m, n>> \in sent
  /\ <<m, n>> \notin acked
  /\ parent[n] = NoNode
  /\ acked' = acked \cup {<<m, n>>}
  /\ pending' = pending \cup {n}
  /\ UNCHANGED <<parent, sent>>

Deliver(n) ==
  /\ n \in pending
  /\ \E m \in Node : <<m, n>> \in acked
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = CHOOSE m \in Node : <<m, n>> \in acked]
  /\ pending' = pending \ {n}
  /\ UNCHANGED <<sent, acked>>

Echo(n) ==
  /\ n # initiator
  /\ parent[n] # NoNode
  /\ \A c \in Node : parent[c] # n
  /\ \E m \in Node :
       /\ m # n
       /\ m # parent[n]
       /\ parent' = [parent EXCEPT ![m] = n]
       /\ sent' = sent \cup {<<m, n>>}
       /\ acked' = acked \ {<<n, m>>}
  /\ UNCHANGED <<pending>>

Next ==
  \/ \E n \in Node, m \in Node : Start(n, m)
  \/ \E m \in Node, n \in Node : SendAck(m, n)
  \/ \E n \in Node : Deliver(n)
  \/ \E n \in Node : Echo(n)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ parent \in [Node -> Parents]
  /\ sent \subseteq Edges
  /\ acked \subseteq Edges
  /\ pending \subseteq Node

AncestorProperties ==
  /\ \A n \in Node \ {initiator} : initiator \in Ancestors(n)
  /\ \A n, m \in Node : (m \in Ancestors(n)) => (n \notin Ancestors(m))

TestSpec == Spec

====