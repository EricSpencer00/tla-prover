---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets
EXTENDS SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(* Initial state, delegated to the algorithm module *)
INIT == SeqReachAlg!INIT

(* Next-state relation, delegated to the algorithm module *)
NEXT == SeqReachAlg!NEXT

(* Helper: type correctness of the state variables *)
TypeCorrect ==
    marked \subseteq Nodes /\ 
    frontier \subseteq Nodes /\ 
    pc \in SeqReachAlg!PCSet

(* Invariant 1: type correctness plus successor property *)
Invariant1 ==
    TypeCorrect /\ 
    \A n \in marked :
        \A s \in SeqReachAlg!Succ[n] :
            s \in marked \/ s \in frontier

(* Invariant 2: relationship between marked, frontier, and reachability *)
Invariant2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

(* Invariant 3: reachability from the root *)
Invariant3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == {Invariant1, Invariant2, Invariant3}

(* Partial‑correctness property: when the algorithm terminates, marked = reachable(Root) *)
TerminationCorrectness ==
    (pc = SeqReachAlg!Done) => (marked = Reachable({Root}))

PROPERTIES == {TerminationCorrectness}

(* The overall specification *)
Spec == INIT /\ [][NEXT]_vars

====