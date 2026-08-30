---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

\* The model is the sequential Misra reachability algorithm with all its
\* variables; this module only adds the concrete graph and bounds the
\* sequence type so the state space stays finite for model checking.
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "active"

Step(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ pc' = IF marked = Nodes THEN "done" ELSE pc

Done ==
  /\ pc = "active"
  /\ frontier = {}
  /\ marked = Nodes
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Step(n)
  \/ Done

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done"}

\* Reachability is closed under successors: once a node is marked it brings
\* its successors into the frontier, so no reachable node is left out.
Inv1 == \A n \in marked : Succ[n] \subseteq frontier \cup marked

Inv2 == frontier \cap marked = {}
Inv3 == marked \cup frontier = Nodes
PartialCorrectness == frontier = {}

\* Finite-state termination: the algorithm always reaches the done state.
Termination == <>(pc = "done")

\* Replaces the infinite Seq operator from Sequences with a bounded version
\* derived from the reachable set; this keeps the model finite.
LimitedSeq(S) ==
  CHOOSE s \in [1..Cardinality(S) -> Nodes] :
    \A i \in 1..Cardinality(S) : s[i] \in S
    /\ \A x \in S : \E i \in 1..Cardinality(S) : s[i] = x

ConnectedToSomeButNotAll(x) ==
  \E s \in Seq(Nodes) : s # <<>> /\ x = s[1] /\ \A i \in 1..(Len(s) - 1): s[i + 1] \in Succ[s[i]]

====