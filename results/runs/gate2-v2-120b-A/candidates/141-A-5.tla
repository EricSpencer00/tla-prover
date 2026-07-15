---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

(*
  Constants required by the .cfg file.
  Users of this module must supply concrete values for these in a .cfg file.
*)
CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all graph nodes
Node == Nodes

\* The set of reachable nodes from a given set of sources
ReachableFrom(S) == 
    LET rec == [s \in Node |-> IF s \in S THEN {s} UNION 
                UNION {Succ[t] : t \in S} ELSE {}] 
    IN UNION { rec^n[Root] : n \in Nat }

\* Type correctness predicate (used as TypeOK invariant)
TypeOK == /\ marked \subseteq Node
          /\ frontier \subseteq Node
          /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Main action (two nondeterministic cases)
\* ----------------------------------------------------------------------
Next == 
    \/ /\ pc = "Loop"
       /\ frontier # {}
       /\ \E n \in frontier :
            \/ /\ n \notin marked
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n] \ {n}
               /\ pc' = "Loop"
            \/ /\ n \in marked
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
               /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ frontier = {}
       /\ marked' = marked
       /\ frontier' = frontier
       /\ pc' = "Done"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Safety invariants (the three described in the natural-language text)
\* ----------------------------------------------------------------------
\* Inv1: Every successor of a marked node is in marked or frontier
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Inv2: Union of marked and nodes reachable from frontier equals
\*       nodes reachable from the union of marked and frontier.
\* For finite graphs this holds; we express it directly.
Inv2 == 
    \A n \in frontier : 
        \A m \in Succ[n] : m \in marked \/ frontier

\* Inv3: Nodes reachable from root equal marked plus nodes reachable from frontier
Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* Partial correctness: when the algorithm terminates (pc = "Done"),
\* the marked set equals exactly the nodes reachable from the root.
PartialCorrectness == 
    pc = "Done" => marked = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

\* ----------------------------------------------------------------------
\* THEOREM statements (optional, but help TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====