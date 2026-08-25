---- MODULE ReachableProofs ----
EXTENDS Nat, TLC, SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* -------------------------------------------------------------------------
\* Type correctness for the algorithm's state variables
\* -------------------------------------------------------------------------
TypeInvariant ==
   marked \subseteq Nodes /\ 
   frontier \subseteq Nodes /\ 
   pc \in {"init", "step", "done"}

\* -------------------------------------------------------------------------
\* Successor relation (assumed to be provided by the algorithm module)
\* -------------------------------------------------------------------------
SuccOf[n \in Nodes] ==
   { m \in Nodes : <<n, m>> \in Edges }

\* -------------------------------------------------------------------------
\* Invariant 1 : every successor of a marked node is already marked or on the frontier
\* -------------------------------------------------------------------------
Inv1 ==
   TypeInvariant /\ 
   \A n \in marked : SuccOf[n] \subseteq marked \cup frontier

\* -------------------------------------------------------------------------
\* Invariant 2 : marked ∪ reachable(frontier) = reachable(marked ∪ frontier)
\* (proved from Lemma 1 in ReachabilityLemmas)
\* -------------------------------------------------------------------------
Inv2 ==
   marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* -------------------------------------------------------------------------
\* Invariant 3 : reachable({Root}) = marked ∪ reachable(frontier)
\* (proved from Lemma 2 and Lemma 3 in ReachabilityLemmas)
\* -------------------------------------------------------------------------
Inv3 ==
   ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* -------------------------------------------------------------------------
\* Collection of all invariants required by TLC
\* -------------------------------------------------------------------------
INVARIANTS == { Inv1, Inv2, Inv3 }

\* -------------------------------------------------------------------------
\* Initial predicate (taken from the sequential reachability algorithm)
\* -------------------------------------------------------------------------
INIT == SeqReachability.Init

\* -------------------------------------------------------------------------
\* Next-state relation (taken from the sequential reachability algorithm)
\* -------------------------------------------------------------------------
NEXT == SeqReachability.Next

\* -------------------------------------------------------------------------
\* Specification of the whole system
\* -------------------------------------------------------------------------
Spec ==
   INIT /\ [] [NEXT]_{<<marked, frontier, pc>>}

\* -------------------------------------------------------------------------
\* Additional properties (none required for this partial‑correctness proof)
\* -------------------------------------------------------------------------
PROPERTIES == {}

====