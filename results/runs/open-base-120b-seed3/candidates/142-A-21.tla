---- MODULE ReachableProofs ----
EXTENDS Naturals, SeqReachAlgo, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(*---  Initial condition  ---------------------------------------------------*)
INIT == SeqReachAlgo.Init

(*---  Next‑state relation  -------------------------------------------------*)
NEXT == SeqReachAlgo.Next

(*---  Specification  -------------------------------------------------------*)
Spec == INIT /\ [][NEXT]_(<<Marked, Frontier, pc>>)

(*---  Invariant 1: type correctness and successor condition --------------*)
Inv1 ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A n \in Marked :
          \A s \in Succ[n] : s \in Marked \/ s \in Frontier

(*---  Invariant 2: marked ∪ reachable(frontier) = reachable(marked∪frontier) *)
Inv2 ==
    Reachable(Marked \cup Frontier) = Marked \cup Reachable(Frontier)

(*---  Invariant 3: reachable from root = marked ∪ reachable(frontier) -----*)
Inv3 ==
    Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS == <<Inv1, Inv2, Inv3>>

(*---  Partial‑correctness property (termination ⇒ marked = reachable) ----*)
Terminated == pc = "Done"
Correctness == Terminated => Marked = Reachable({Root})

PROPERTIES == <<Correctness>>

====