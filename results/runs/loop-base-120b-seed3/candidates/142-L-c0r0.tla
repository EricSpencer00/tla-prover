---- MODULE ReachableProofs ----
EXTENDS SeqReachability, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* State initialization and transition relation are taken from the
\* sequential reachability algorithm module.
\* ----------------------------------------------------------------------
Init == SeqReachability!Init

Next == SeqReachability!Next

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor condition
\* ----------------------------------------------------------------------
Inv1 ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ \A n \in Marked :
        \A s \in Succ[n] : s \in Marked \/ s \in Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: relationship between marked, frontier and reachability
\* ----------------------------------------------------------------------
Inv2 ==
  (Marked \cup ReachableFrom(Frontier)) = ReachableFrom(Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: marked set equals reachable nodes from the root
\* ----------------------------------------------------------------------
Inv3 ==
  ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

\* ----------------------------------------------------------------------
\* Conjunction of all invariants
\* ----------------------------------------------------------------------
Invariants == Inv1 /\ Inv2 /\ Inv3

\* ----------------------------------------------------------------------
\* Safety property: when the algorithm terminates, marked = reachable
\* ----------------------------------------------------------------------
Property ==
  (pc = "Done") => (Marked = ReachableFrom({Root}))

Properties == Property

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<Marked, Frontier, pc>> /\ Invariants

====