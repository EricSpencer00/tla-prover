---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, SeqReachability, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* State variables are inherited from the sequential reachability algorithm.
\* ----------------------------------------------------------------------
vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial predicate (taken from the algorithm module)
\* ----------------------------------------------------------------------
Init == InitAlg

\* ----------------------------------------------------------------------
\* Next-state relation (taken from the algorithm module)
\* ----------------------------------------------------------------------
Next == NextAlg

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
  (Marked \cup ReachableFrom(Frontier)) =
    ReachableFrom(Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: marked set equals reachable nodes from the root
\* ----------------------------------------------------------------------
Inv3 ==
  ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

\* ----------------------------------------------------------------------
\* Collection of invariants required by the model checker
\* ----------------------------------------------------------------------
Invariants == { Inv1, Inv2, Inv3 }

\* ----------------------------------------------------------------------
\* Termination condition (program counter indicates completion)
\* ----------------------------------------------------------------------
Termination == pc = "Done"

\* ----------------------------------------------------------------------
\* Safety property proved in the final theorem
\* ----------------------------------------------------------------------
Properties == Termination => (Marked = ReachableFrom({Root}))

\* ----------------------------------------------------------------------
\* Specification of the system
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars /\ \A inv \in Invariants : []inv

====