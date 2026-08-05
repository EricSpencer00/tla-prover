---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node

VARIABLES parent, children, visited, acked, phase

vars == <<parent, children, visited, acked, phase>>

TypeInv ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ visited \in [Node -> 0..4]
  /\ acked \in [Node -> BOOLEAN]
  /\ phase \in {"init", "searching", "done"}

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ visited = [n \in Node |-> 0]
  /\ acked = [n \in Node |-> FALSE]
  /\ phase = "init"

Explore(n, m) ==
  /\ phase = "searching"
  /\ parent[n] = NoNode
  /\ <<n, m>> \in R
  /\ visited[m] < 4
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ children' = [children EXCEPT ![m] = @ \cup {n}]
  /\ visited' = [visited EXCEPT ![m] = 1 + @]
  /\ UNCHANGED <<acked, phase>>

Ack(m) ==
  /\ phase = "searching"
  /\ parent[m] # NoNode
  /\ ~acked[m]
  /\ acked' = [acked EXCEPT ![m] = TRUE]
  /\ visited' = [visited EXCEPT ![m] = 0]
  /\ UNCHANGED <<parent, children, phase>>

Quit ==
  /\ phase = "searching"
  /\ \A m \in Node : acked[m]
  /\ phase' = "done"
  /\ UNCHANGED <<parent, children, visited, acked>>

Trigger ==
  /\ phase = "init"
  /\ phase' = "searching"
  /\ UNCHANGED <<parent, children, visited, acked>>

Next ==
  \/ \E n, m \in Node : Explore(n, m)
  \/ \E m \in Node : Ack(m)
  \/ Quit
  \/ Trigger

Spec == Init /\ [][Next]_vars

Ancestors == {p \in Node : (p # initiator /\ p \in children[initiator]) \/ (parent[p] = initiator)}
AncestorProperties ==
  /\ (phase = "done" => Nodes \ {initiator} \subseteq Ancestors)
  /\ \A a \in Node : a # NoNode => parent[parent[a]] # a

PrintGraph ==
  /\ (UNION { R })
  /\ TRUE

====