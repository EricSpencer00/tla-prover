---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Misra's variant of BFS: the visited (marked) set and the frontier may overlap.
\* The safety invariants relate the marked set and frontier to the reachable
\* subgraph; they are not derivable from each other and jointly imply partial
\* correctness of the reachable set computed by the algorithm.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Nondeterministically pick a frontier node and explore it. If it is new, mark
\* it and add its successors to the frontier without removing it; if it is
\* already marked, simply remove it from the frontier.
Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore(Root)) /\ WF_vars(Terminate)

\* Every successor of a marked node is either already marked or still in the
\* frontier: frontier nodes are never lost before they are explored.
Inv1 ==
  \A n \in Nodes : n \in marked => \A m \in Succ[n] : (m \in marked) \/ (m \in frontier)

\* The nodes reachable from the marked set together with those reachable
\* from the frontier are exactly those reachable from their union -- no node
\* becomes reachable only through the frontier without being reachable from
\* the marked set, and none is lost from both sides.
Inv2 ==
  (ReachableFrom(marked) \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)

\* The reachable nodes from the root decompose into the marked set and the
\* remainder reachable from the frontier.
Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == ReachableFrom({Root}) = marked

Termination == (frontier # {}) ~> (frontier = {})

\* Operator that the .cfg substitutes for Succ; it is a bounded version of the
\* graph's successor relation and keeps the reachable set finite for checking.
ConnectedToSomeButNotAll(n) == Succ[n]

\* Operator that the .cfg substitutes for Seq (a finite version of Sequences.seq).
LimitedSeq(S) == CHOOSE s \in Seq(S) : \A x \in S : (\E i \in DOMAIN s : s[i] = x)

====