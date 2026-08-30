---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* The configuration module for the sequential Misra reachability algorithm.
\* It inherits the algorithm's state and actions, and adds the concrete
\* graph structure and a bounded sequence override so the model is finite.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

\* The algorithm's core step: expand the frontier by one successor of a
\* marked node that is not yet marked, then mark it.
Step ==
  /\ pc # "done"
  /\ \E n \in frontier, m \in Succ[n] :
       /\ m \notin marked
       /\ marked' = marked \cup {m}
       /\ frontier' = (frontier \ {n}) \cup {m}
  /\ pc' = IF frontier = {} THEN "done" ELSE "working"

\* The algorithm is deterministic once the frontier is empty, so it simply
\* idles in the done state.
Done ==
  /\ pc = "done"
  /\ pc' = pc
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

\* Successor closure: every marked node's successors are all marked.
Inv1 == \A n \in marked : Succ[n] \subseteq marked

\* Reachability decomposition: the marked set is exactly the root plus
\* the successors of the marked set.
Inv2 == marked = {Root} \cup (UNION {Succ[n] : n \in marked})

\* Reachable set equality: the marked set is exactly the set of nodes
\* reachable from the root by some path.
Inv3 ==
  \A n \in Nodes :
    n \in marked <=> \E s \in LimitedSeq(Nodes) :
      /\ Len(s) >= 1
      /\ s[1] = Root
      /\ s[Len(s)] = n
      /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]

PartialCorrectness == marked = Nodes

Termination == <>(pc = "done")

\* The .cfg file substitutes ConnectedToSomeButNotAll for Succ, so this
\* operator must exist and be a finite, deterministic version of Succ.
ConnectedToSomeButNotAll(n) == Succ[n]

\* The .cfg file substitutes LimitedSeq for Seq, so this operator must
\* exist and be a FINITE version of Seq (keeping EXTENDS Sequences).
LimitedSeq(S) == Seq(S)

====