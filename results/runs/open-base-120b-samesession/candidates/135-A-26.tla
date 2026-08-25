---- MODULE MCReachable ----
EXTENDS Sequences, Naturals, FiniteSets, ReachabilityAlg

\*-------------------------------------------------
\* Constants required by the configuration
\*-------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*-------------------------------------------------
\* Concrete graph structure (overridden by the .cfg)
\*-------------------------------------------------
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 1 -> {2, 3}
        [] n = 2 -> {3, 4}
        [] n = 3 -> {1, 4}
        [] n = 4 -> {1, 2}
  ]

\*-------------------------------------------------
\* Bounded sequence operator (replaces Seq)
\*-------------------------------------------------
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\*-------------------------------------------------
\* State variables (inherited from ReachabilityAlg)
\*-------------------------------------------------
VARIABLES marked, frontier, pc

\*-------------------------------------------------
\* Helper definitions
\*-------------------------------------------------
Vars == << marked, frontier, pc >>

\* Reachable nodes via bounded paths from Root
Reachable ==
  { n \in Nodes :
      \E p \in LimitedSeq :
        /\ Len(p) > 0
        /\ Head(p) = Root
        /\ Last(p) = n
        /\ \A i \in 1 .. Len(p)-1 :
              p[i+1] \in ConnectedToSomeButNotAll[p[i]]
  }

\*-------------------------------------------------
\* Specification
\*-------------------------------------------------
Spec == Init /\ [][Next]_Vars

\*-------------------------------------------------
\* Invariants
\*-------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

\* Successor closure: every marked node's successors are also marked
Inv1 ==
  \A n \in marked :
    \A s \in ConnectedToSomeButNotAll[n] :
      s \in marked

\* Reachability decomposition: frontier nodes are exactly those
\* marked but not yet explored
Inv2 ==
  frontier = marked \ { n \in Nodes : n \in explored }

\* Reachable set equality: when the algorithm terminates,
\* the marked set equals the set of all nodes reachable from Root
Inv3 ==
  (pc = "done") => (marked = Reachable)

\* Partial correctness: if the algorithm finishes, marked is the reachable set
PartialCorrectness ==
  (pc = "done") => (marked = Reachable)

\*-------------------------------------------------
\* Liveness property (termination)
\*-------------------------------------------------
Termination == <> (pc = "done")

====