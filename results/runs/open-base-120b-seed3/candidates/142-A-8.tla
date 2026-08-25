---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, GraphTheory, SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(*--- Initial state ---------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

(*--- Transition relation ---------------------------------------------*)
Next ==
    \/ /\ pc = "idle"
       /\ frontier # {}
       /\ \E n \in frontier :
            LET newMarked   == marked \cup {n}
                newFrontier == (frontier \ {n}) \cup
                               { s \in Nodes : s \in Succ[n] /\ s \notin marked }
            IN /\ marked'   = newMarked
               /\ frontier' = newFrontier
               /\ pc'       = "idle"
    \/ /\ pc = "idle"
       /\ frontier = {}
       /\ marked'   = marked
       /\ frontier' = frontier
       /\ pc'       = "done"

(*--- Invariant 1: type correctness and successor condition ----------*)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
          \A s \in Succ[n] : s \in marked \/ s \in frontier

(*--- Invariant 2: reachable-from frontier ----------------------------*)
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

(*--- Invariant 3: marked set equals reachable from root -------------*)
Inv3 ==
    Reachable(Root) = marked \cup ReachableFrom(frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

(*--- Final correctness property --------------------------------------*)
FinalCorrectness ==
    /\ pc = "done"
    => marked = Reachable(Root)

PROPERTIES == FinalCorrectness

Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

====