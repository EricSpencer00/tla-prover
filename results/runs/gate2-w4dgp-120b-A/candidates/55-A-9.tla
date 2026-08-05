---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, tree, recvCount, phase

vars == <<parent, tree, recvCount, phase>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ tree \in [Node -> SUBSET (Node \times Node)]
  /\ recvCount \in [Node -> Nat]
  /\ phase \in [Node -> {"idle", "exploring", "done"}]

AncestorProperties ==
  /\ \A n \in Node : n # initiator => initiator \in parent[n]
  /\ \A m, n \in Node : m \in parent[n] => parent[m] # n

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ tree = [n \in Node |-> {}]
  /\ recvCount = [n \in Node |-> 0]
  /\ phase = [n \in Node |-> IF n = initiator THEN "exploring" ELSE "idle"]

Explore(n) ==
  /\ phase[n] = "exploring"
  /\ \E m \in Node :
       /\ m # n
       /\ m \notin parent[n]
       /\ parent' = [parent EXCEPT ![m] = n]
       /\ tree' = [tree EXCEPT ![n] = tree[n] \cup {<<n, m>>}]
       /\ recvCount' = [recvCount EXCEPT ![m] = recvCount[m] + 1]
  /\ UNCHANGED phase

Echo(n) ==
  /\ phase[n] = "idle"
  /\ \E m \in Node :
       /\ m # n
       /\ parent[n] = m
       /\ parent' = [parent EXCEPT ![n] = NoNode]
       /\ tree' = [tree EXCEPT ![n] = {}]
       /\ recvCount' = [recvCount EXCEPT ![n] = 0]
  /\ phase' = [phase EXCEPT ![n] = "done"]

Return(n) ==
  /\ phase[n] = "exploring"
  /\ \A m \in Node : n \in tree[m]
  /\ parent' = [parent EXCEPT ![n] = NoNode]
  /\ tree' = [tree EXCEPT ![n] = {}]
  /\ phase' = [phase EXCEPT ![n] = "idle"]
  /\ UNCHANGED recvCount

AllReturned == \A n \in Node : phase[n] = "done"

Next == \E n \in Node : Explore(n) \/ Echo(n) \/ Return(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Node : Echo(n))

PrintGraph ==
  /\ \A x \in Node : \E y \in Node : <<x, y>> \in R
  /\ \A x, y \in Node : (<<x, y>> \in R) => (x # y)
  /\ \A x, y \in Node : (<<x, y>> \in R) <=> (<<y, x>> \in R)
  /\ \A n \in Node : parent[n] \in Node \cup {NoNode}
  /\ UNCHANGED vars

TestSpec == Spec /\ PrintGraph

====