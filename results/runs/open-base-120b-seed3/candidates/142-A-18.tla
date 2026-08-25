---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, SeqReachAlg, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(*--- Type constraints ---------------------------------------------------*)
TypeInvariant == /\ Marked \subseteq Nodes
                 /\ Frontier \subseteq Nodes

(*--- Graph-theoretic helpers (imported from ReachabilityProofs) ----------*)
Successors(n) == ReachabilityProofs.Successors(n)

Reachable(S) == ReachabilityProofs.Reachable(S)

(*--- Initial state (delegated to the algorithm module) -------------------*)
INIT == SeqReachAlg.Init

(*--- Next-state relation (delegated to the algorithm module) ------------*)
NEXT == SeqReachAlg.Next

(*--- Specification -------------------------------------------------------*)
Spec == INIT /\ [][NEXT]_<<Marked, Frontier, pc>>

(*--- Invariant 1: type correctness and successor condition -------------*)
Inv1 == /\ TypeInvariant
        /\ \A n \in Marked :
               \A s \in Successors(n) : s \in Marked \/ s \in Frontier

(*--- Invariant 2: reachable-from frontier vs. reachable-from union -----*)
Inv2 == Reachable(Frontier) \cup Marked = Reachable(Marked \cup Frontier)

(*--- Invariant 3: reachable-from root equals marked ∪ reachable frontier *)
Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS == << Inv1, Inv2, Inv3 >>

(*--- Termination predicate (algorithm‐specific) ------------------------*)
Terminated == pc = "done"

(*--- Partial correctness theorem ----------------------------------------*)
PartialCorrectness == Terminated => Marked = Reachable({Root})

PROPERTIES == << PartialCorrectness >>

====