---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

EXTENDS MisraReachability, ReachabilityProofsBase

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, PC

\* Import the definitions from the sequential algorithm
Init == MisraReachability.Init
Next == MisraReachability.Next

\* The specification of the system
Spec == Init /\ [][Next]_<<Marked, Frontier, PC>>

\* Reachability function supplied by the reachability‑proofs module
ReachableFrom == ReachabilityProofsBase.ReachableFrom
ReachableSet == ReachableFrom({Root})

\* Invariant 1 : type correctness and every successor of a marked node
Inv1 == 
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A n \in Marked : \A m \in Adj[n] : m \in Marked \/ m \in Frontier

\* Invariant 2 : marked set plus nodes reachable from the frontier equals
\*                nodes reachable from the union of marked and frontier
Inv2 ==
    Marked \cup ReachableFrom(Frontier) = ReachableFrom(Marked \cup Frontier)

\* Invariant 3 : reachable set from the root equals marked set plus nodes
\*                reachable from the frontier
Inv3 == ReachableSet = Marked \cup ReachableFrom(Frontier)

\* Termination condition (placeholder – depends on the algorithm’s final state)
Terminated == (PC = "Done")

\* Partial‑correctness theorem: upon termination the marked set equals the reachable set
THEOREM PartialCorrectness == Terminated => Marked = ReachableSet

====