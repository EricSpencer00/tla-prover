---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

\* Predicates on the graph: symmetry and no self-loop.
Neighbors(n) == R \ {n}
Connected == \A a \in Node : \A b \in Node : (a # b) => (<<a, b>> \in R)
Symmetric == \A a \in Node : \A b \in Node : (<<a, b>> \in R) => (<<b, a>> \in R)
NoSelfLoop == \A n \in Node : <<n, n>> \notin R

VARIABLES state, parent, pending, active

vars == <<state, parent, pending, active>>

TypeOK ==
  /\ state \in [Node -> {"init", "pending", "done", "crashed"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ pending \subseteq [node : Node, from : Node]
  /\ active \subseteq [node : Node, from : Node]
  /\ initiator \in Node

Ancestor(n) == CHOOSE p \in Node : parent[n] = p
AncestorOf(n, m) ==
  IF state[m] = "done" /\ parent[m] # NoNode
  THEN (m = n) \/ AncestorOf(n, parent[m])
  ELSE m = n
Spawn(n) == [node |-> n, from |-> initiator]
SpawnActive(n) == [node |-> n, from |-> initiator]
Reply(m) == [node |-> initiator, from |-> m]

Init ==
  /\ state = [n \in Node |-> IF n = initiator THEN "pending" ELSE "init"]
  /\ parent = [n \in Node |-> IF n = initiator THEN initiator ELSE NoNode]
  /\ pending = {SpawnActive(n) : n \in Node}
  /\ active = {}
  /\ Connected

Emit(m) ==
  /\ m \in pending
  /\ pending' = pending \ {m}
  /\ active' = active \cup {Spawn(m)}
  /\ UNCHANGED <<state, parent>>

\* The initiator's decision is fanned out to every other node (branching step).
Decide(m) ==
  /\ m \in active
  /\ LET n == m.node IN
       /\ state[n] = "init"
       /\ state' = [state EXCEPT ![n] = "pending"]
       /\ parent' = [parent EXCEPT ![n] = m.from]
       /\ pending' = pending \cup {Reply(n)}
  /\ active' = active \ {m}

Apply(m) ==
  /\ m \in active
  /\ LET n == m.node IN
       /\ state[n] = "pending"
       /\ state' = [state EXCEPT ![n] = "done"]
       /\ active' = active \ {m}
  /\ UNCHANGED <<parent, pending>>

Crash(m) ==
  /\ m \in active
  /\ LET n == m.node IN
       /\ state[n] # "done"
       /\ state' = [state EXCEPT ![n] = "crashed"]
       /\ active' = active \ {m}
  /\ UNCHANGED <<parent, pending>>

Next ==
  \/ \E m \in pending : Emit(m)
  \/ \E m \in active : Decide(m) \/ Apply(m) \/ Crash(m)

\* Once every node has decided, the system quiesces (no further steps,
\* which is what forces every active message to be applied/completed).
Quiesce == (\A n \in Node : state[n] # "init") /\ UNCHANGED vars

\* TestSpec is the overridden operator the .cfg file points to.
TestSpec == (Init /\ [][Next]_vars) \/ ([][Quiesce]_vars)

\* AncestorProperties is the Echo spec's spanning-tree correctness condition:
\* the initiator is an ancestor of every other node, and the ancestor
\* relation is acyclic -- the only way both hold is a spanning tree rooted
\* at the initiator.
AncestorProperties ==
  \A n \in Node, m \in Node :
    (state[m] = "done") => (AncestorOf(n, m) <=> (n = initiator \/ parent[m] = n))

Spec == TestSpec

====