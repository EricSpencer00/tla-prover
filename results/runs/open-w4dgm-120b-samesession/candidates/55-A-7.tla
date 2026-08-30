---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, children, pending, active
vars == <<parent, children, pending, active>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ pending \subseteq (Node \X Node)
  /\ active \in [Node -> BOOLEAN]

InitiatorParent ==
  /\ parent[initiator] = NoNode
  /\ \E c \in children[initiator] : c # initiator

Ancestor(x, y) ==
  IF x = y THEN TRUE
  ELSE LET p == parent[x] IN IF p = NoNode THEN FALSE ELSE Ancestor(p, y)

AncestorProperties ==
  /\ InitiatorParent
  /\ \A x \in Node : x # initiator => Ancestor(x, initiator)
  /\ \A x \in Node : \A y \in Node : (Ancestor(x, y) /\ y # x) => ~Ancestor(y, x)

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ pending = {}
  /\ active = [n \in Node |-> FALSE]

Send(n, m) ==
  /\ parent[n] = NoNode
  /\ m \notin children[n]
  /\ n # m
  /\ <<n, m>> \notin pending
  /\ pending' = pending \cup {<<n, m>>}
  /\ UNCHANGED <<parent, children, active>>

Deliver(n, m) ==
  /\ <<n, m>> \in pending
  /\ active[m] = FALSE
  /\ pending' = pending \ {<<n, m>>}
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ children' = [children EXCEPT ![n] = @ \cup {m}]
  /\ UNCHANGED active

Activate(n) ==
  /\ parent[n] # NoNode
  /\ active[n] = FALSE
  /\ active' = [active EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, children, pending>>

Idle == UNCHANGED vars

Next ==
  \/ \E n \in Node, m \in Node : Send(n, m) \/ Deliver(n, m)
  \/ \E n \in Node : Activate(n)
  \/ Idle

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Node, m \in Node : Deliver(n, m))
  /\ WF_vars(\E n \in Node : Activate(n))

TestSpec == Spec

N1 == Node
I1 == initiator
R1 == R
====