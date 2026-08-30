---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES infused, expect, pending, ready, parent, started

vars == <<infused, expect, pending, ready, parent, started>>

TypeOK ==
  /\ infused \subseteq Node
  /\ expect \subseteq Node
  /\ pending \subseteq (Node \X Node)
  /\ ready \subseteq Node
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ started \in BOOLEAN

Init ==
  /\ infused = {}
  /\ expect = {}
  /\ pending = {}
  /\ ready = {}
  /\ parent = [n \in Node |-> NoNode]
  /\ started = FALSE

Start ==
  /\ ~ started
  /\ started' = TRUE
  /\ expect' = {initiator}
  /\ UNCHANGED <<infused, pending, ready, parent>>

SendEcho(n, m) ==
  /\ n \in ready
  /\ <<n, m>> \notin pending
  /\ parent[m] = NoNode
  /\ n # m
  /\ pending' = pending \cup {<<n, m>>}
  /\ UNCHANGED <<infused, expect, ready, parent, started>>

DeliverEcho(n, m) ==
  /\ started
  /\ <<n, m>> \in pending
  /\ ready' = ready \cup {m}
  /\ pending' = pending \ {<<n, m>>}
  /\ UNCHANGED <<infused, expect, parent, started>>

Infuse(n) ==
  /\ n \in ready
  /\ n \notin infused
  /\ infused' = infused \cup {n}
  /\ UNCHANGED <<expect, pending, ready, parent, started>>

SetParent(c, n) ==
  /\ c \in expect
  /\ c \notin infused
  /\ parent[n] = NoNode
  /\ n # c
  /\ parent' = [parent EXCEPT ![n] = c]
  /\ expect' = expect \cup {n}
  /\ UNCHANGED <<infused, pending, ready, started>>

Quiesce ==
  /\ \A n \in Node : n \in infused
  /\ UNCHANGED vars

Next ==
  \/ Start
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E n \in Node, m \in Node : DeliverEcho(n, m)
  \/ \E n \in Node : Infuse(n)
  \/ \E c \in Node, n \in Node : SetParent(c, n)
  \/ Quiesce

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ (initiator \in infused) <=> (expect \subseteq infused)
  /\ (initiator \in infused) =>
       \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A n \in Node, m \in Node :
       (parent[n] = m /\ n # initiator) => (n \notin expect \/ m \in expect)

PrintGraph ==
  /\ started = FALSE
  /\ started' = TRUE
  /\ UNCHANGED <<infused, expect, pending, ready, parent>>
  /\ \E dummy \in {1} : UNCHANGED started

TestSpec == Spec /\ PrintGraph

====