---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root

(*--------------------------------------------------------------------
  Types and basic definitions (graph of nodes and edges)
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(* The set of edges of the graph, to be instantiated by the .cfg *)
Edges == {}

(* The set of successors of a node *)
Succ(n) == { m \in Nodes : <<n, m>> \in Edges }

(* Reachable nodes from a given set using the graph defined by Edges *)
Reachable(S) ==
    LET
        R == [n \in Nodes |-> FALSE]
    IN
        CHOOSE X \subseteq Nodes :
            /\ X = S \cup { y \in Nodes :
                    \E x \in X : y \in Succ(x) }

(*--------------------------------------------------------------------
  Initial predicate
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(*--------------------------------------------------------------------
  Algorithm actions (placeholders for the sequential algorithm)
--------------------------------------------------------------------*)
StepAdd ==
    /\ pc = "Init"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (Succ(n) \ marked)
        /\ pc' = "Running"

StepDone ==
    /\ pc = "Running"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

(* No other actions are modeled *)
Next ==
    \/ StepAdd
    \/ StepDone

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier

Inv2 ==
    /\ Reachable(marked) \cup Reachable(frontier) =
       Reachable(marked \cup frontier)

Inv3 ==
    /\ Reachable({Root}) = marked \cup Reachable(frontier)

(*--------------------------------------------------------------------
  Theorem (partial correctness)
--------------------------------------------------------------------*)
TerminationCorrectness ==
    ASSUME Spec
    PROVE
        /\ [] (pc = "Done" => marked = Reachable({Root}))
        /\ [] (pc = "Done" => frontier = {})

====