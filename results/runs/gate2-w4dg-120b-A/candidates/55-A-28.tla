---- MODULE MCEcho ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, done, visited, m
vars == <<parent, done, visited, m>>

Undirected(r) == \A x \in Node, y \in Node : r[x, y] => r[y, x]
Irrefl(r) == \A x \in Node : ~r[x, x]
Connected(r) == \A x \in Node : \E y \in Node : r[x, y]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ done = [n \in Node |-> FALSE]
  /\ visited = [n \in Node |-> FALSE]
  /\ m = FALSE

Send(n) ==
  /\ n = initiator
  /\ ~visited[n]
  /\ visited' = [visited EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, done, m>>

Echo(n) ==
  /\ \E x \in Node :
       /\ visited[x]
       /\ visited[n] = FALSE
       /\ parent[n] = NoNode
       /\ parent' = [parent EXCEPT ![n] = x]
  /\ visited' = [visited EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<done, m>>

Terminate ==
  /\ done' = [n \in Node |-> visited[n]]
  /\ UNCHANGED <<parent, visited, m>>

SwitchMode ==
  /\ ~m
  /\ m' = TRUE
  /\ UNCHANGED <<parent, done, visited>>

InitStep == Send(initiator) \/ Echo(initiator)
EchoStep == \E n \in Node : Echo(n)
Next == InitStep \/ EchoStep \/ Terminate \/ SwitchMode

Spec == Init /\ [][Next]_vars
TestSpec == Spec /\ SwitchMode

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ done \in [Node -> BOOLEAN]
  /\ visited \in [Node -> BOOLEAN]
  /\ m \in BOOLEAN

Ancestor(n, x) ==
  \/ parent[n] = x
  \/ \E y \in Node : parent[n] = y /\ Ancestor(y, x)

AncestorProperties ==
  /\ \A n \in Node : n # initiator => Ancestor(n, initiator)
  /\ \A n \in Node, x \in Node :
       (Ancestor(n, x) /\ parent[x] = NoNode) => x = initiator

====