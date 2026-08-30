---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

NoNode == "none"

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", NoNode}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "working"

\* The reachability step is a nondeterministic choice of any frontier node and
\* any one of its successors, executed under mutual exclusion (the "pc" lock).
Reach ==
  /\ pc = "working"
  /\ frontier # {}
  /\ \E n \in frontier, m \in Succ[n]:
       /\ marked' = marked \cup {m}
       /\ frontier' = (frontier \ {n}) \cup {m}
  /\ UNCHANGED pc

Reset ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = NoNode
  /\ UNCHANGED <<marked, frontier>>

Restart ==
  /\ pc = NoNode
  /\ pc' = "working"
  /\ UNCHANGED <<marked, frontier>>

Next == Reach \/ Reset \/ Restart

Spec == Init /\ [][Next]_vars /\ WF_vars(Reset) /\ WF_vars(Restart)

\* Reachability is defined by existentially quantified paths; the override below
\* makes the path set finite, which is what keeps the reachable state space finite.
Reachable ==
  {n \in Nodes :
     \E k \in 0..Cardinality(Nodes), p \in LimitedSeq(Nodes):
       /\ Len(p) = k
       /\ p[1] = Root
       /\ p[k] = n
       /\ \A i \in 1..(k - 1): p[i + 1] \in Succ[p[i]]}

\* Bounded "any successor" instead of full nondeterministic choice: the two
\* successors are ordered, and this picks the first one, keeping the reachable
\* set closed under at least one concrete transition out of every frontier node.
ConnectedToSomeButNotAll == {b \in Nodes : \E a \in Nodes: b \in Succ[a]}

Inv1 == frontier \subseteq marked
Inv2 == marked \subseteq ConnectedToSomeButNotAll
Inv3 == marked = Reachable
PartialCorrectness == Root \in Reachable

Termination == <> (pc = NoNode)

\* Bounded version of Seq: the domain is a finite range rather than the whole
\* natural numbers, which stops the model checking from chasing infinite paths.
LimitedSeq(S) ==
  {f \in [1..Cardinality(Nodes) -> S] :
     \A x \in 1..Cardinality(Nodes): x <= Len(f) => f[x] \in S}

====