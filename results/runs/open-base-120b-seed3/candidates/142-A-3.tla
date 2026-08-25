---- MODULE ReachableProofs ----
EXTENDS Naturals, TLC

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(* Include the sequential reachability algorithm and the graph‑theoretic lemmas *)
INSTANCE SeqReachAlg
INSTANCE ReachabilityLemmas

(*---------------------------------------------------------------*)
(* State predicates *)

INIT == SeqReachAlg!Init
NEXT == SeqReachAlg!Next

Vars == <<Marked, Frontier, pc>>

Spec == INIT /\ [][NEXT]_Vars

(*---------------------------------------------------------------*)
(* Definitions imported from the lemmas module *)

Succ == ReachabilityLemmas!Succ          \* successor relation: Succ[n] is the set of successors of n
Reachable == ReachabilityLemmas!Reachable  \* Reachable(S) = nodes reachable from set S

(*---------------------------------------------------------------*)
(* Invariant 1: type correctness and successor condition *)

TypeCorrectness ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in SeqReachAlg!PCVals

Inv1 ==
    /\ TypeCorrectness
    /\ \A n \in Marked :
          \A s \in Succ[n] : s \in Marked \/ s \in Frontier

(*---------------------------------------------------------------*)
(* Invariant 2: marked ∪ reachable(Frontier) = reachable(marked ∪ Frontier) *)

Inv2 == (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

(*---------------------------------------------------------------*)
(* Invariant 3: reachable from the root equals marked ∪ reachable(Frontier) *)

Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS == <<Inv1, Inv2, Inv3>>

(*---------------------------------------------------------------*)
(* Partial‑correctness property (the final theorem) *)

PartialCorrectness == [] (pc = "Done" => Marked = Reachable({Root}))

PROPERTIES == PartialCorrectness

====