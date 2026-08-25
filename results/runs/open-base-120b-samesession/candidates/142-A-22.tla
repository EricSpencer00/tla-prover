---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants required by the configuration
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*--------------------------------------------------------------------
  Graph definition (assumed to be provided elsewhere or instantiated)
--------------------------------------------------------------------*)
(* Edge is a binary relation on Nodes representing the graph's arcs. *)
VARIABLE Edge

(*--------------------------------------------------------------------
  State variables of the sequential reachability algorithm
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* Reachable(S) = set of nodes reachable from any node of S via Edge
Reachable(S) ==
  { n \in Nodes :
      \E s \in S :
        <<s, n>> \in TransitiveClosure(Edge) }

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"
  /\ Edge \subseteq Nodes \X Nodes

(*--------------------------------------------------------------------
  Next-state relation (a simple BFS step)
--------------------------------------------------------------------*)
Next ==
  \/ /\ pc = "run"
     /\ \E n \in frontier:
          /\ marked' = marked \cup {n}
          /\ frontier' =
               (frontier \ {n}) \cup
               { m \in Nodes : <<n, m>> \in Edge }
          /\ pc' = IF frontier' = {} THEN "done" ELSE "run"
          /\ UNCHANGED Edge
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc, Edge>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
Invariant1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}
  /\ \A n \in marked :
        \A m \in Nodes :
          <<n, m>> \in Edge => m \in marked \/ m \in frontier

Invariant2 ==
  marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Invariant3 ==
  Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == <<Invariant1, Invariant2, Invariant3>>

(*--------------------------------------------------------------------
  Properties (partial correctness theorem)
--------------------------------------------------------------------*)
TerminationCorrectness ==
  [] (pc = "done" => marked = Reachable({Root}))

PROPERTIES == <<TerminationCorrectness>>

====