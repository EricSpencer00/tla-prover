---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

N1 == initiator
I1 == initiator
R1 == R

ASSUME /\ NoNode \notin Node
       /\ initiator \in Node
       /\ \A x, y \in Node : (x, y) \in R <=> (y, x) \in R
       /\ \A x \in Node : (x, x) \notin R
       /\ \A x \in Node : \E y \in Node \ {x} : <<x, y>> \in R

VARIABLES parent, done, phase

vars == <<parent, done, phase>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ done \in 0..3
  /\ phase \in {"init", "echo"}

AncestorProperties ==
  /\ \A x \in Node : x # initiator => (parent[x] # NoNode /\ parent[x] # x)
  /\ \A x \in Node : (parent[x] = initiator) \/ (parent[x] # NoNode /\ parent[parent[x]] = initiator)

Init ==
  /\ parent = [x \in Node |-> NoNode]
  /\ done = 0
  /\ phase = "init"

Echo(x) ==
  /\ phase = "init"
  /\ parent[x] = NoNode
  /\ x # initiator
  /\ \E y \in Node : y # x /\ <<x, y>> \in R /\ parent' = [parent EXCEPT ![x] = y]
  /\ UNCHANGED <<done, phase>>

EchoBack(x) ==
  /\ phase = "init"
  /\ parent[x] # NoNode
  /\ x # initiator
  /\ done < 3
  /\ done' = done + 1
  /\ UNCHANGED <<parent, phase>>

Initiate ==
  /\ phase = "init"
  /\ done = 3
  /\ phase' = "echo"
  /\ UNCHANGED <<parent, done>>

Terminate ==
  /\ phase = "echo"
  /\ done' = 0
  /\ UNCHANGED <<parent, phase>>

Next ==
  \/ \E x \in Node : Echo(x)
  \/ \E x \in Node : EchoBack(x)
  \/ Initiate
  \/ Terminate

Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ (Print("Graph edges:") /\ \A x \in Node : \A y \in Node : IF <<x, y>> \in R THEN Print("  " ^ x ^ " -- " ^ y) ELSE Skip)

====