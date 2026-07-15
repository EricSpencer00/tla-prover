---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

(* ------------------------------------------------------------------------- *)
(* Constants required by the configuration                                   *)
(* ------------------------------------------------------------------------- *)
CONSTANT Nodes
CONSTANT Root

(* ------------------------------------------------------------------------- *)
(* Derived definitions                                                       *)
(* ------------------------------------------------------------------------- *)
Node == Nodes

(* ------------------------------------------------------------------------- *)
(* State variables                                                          *)
(* ------------------------------------------------------------------------- *)
VARIABLES marked, frontier, pc

(* ------------------------------------------------------------------------- *)
(* Helper definitions (graph edges must be supplied as a constant elsewhere) *)
(* ------------------------------------------------------------------------- *)
\* The graph can be modelled by a relation Edges that maps each node to its
\* set of successors.  For the purposes of this module we leave it abstract.
\* Concrete models must assign a concrete function to Edges.
Edges == [n \in Node |-> {}]

\* Successors of a set of nodes
Succ(S) == UNION { Edges[n] : n \in S }

(* ------------------------------------------------------------------------- *)
(* Type correctness invariant                                                *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ pc \in {"Start", "Explore", "Done"}

(* ------------------------------------------------------------------------- *)
(* Invariant 1: every successor of a marked node is either marked or in the frontier *)
(* ------------------------------------------------------------------------- *)
Inv1 == \A n \in marked : Edges[n] \subseteq marked \cup frontier

(* ------------------------------------------------------------------------- *)
(* Invariant 2: marked ∪ Reachable(frontier) equals Reachable(marked ∪ frontier) *)
(* ------------------------------------------------------------------------- *)
\* Reachable set from a given set of nodes (standard graph reachability)
Reachable(S) ==
    LET Rec(S) ==
        IF S = {} THEN {}
        ELSE S \cup Rec(Succ(S))
    IN Rec(S)

Inv2 == marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

(* ------------------------------------------------------------------------- *)
(* Invariant 3: reachable from the root equals marked ∪ Reachable(frontier) *)
(* ------------------------------------------------------------------------- *)
Inv3 == Reachable({Root}) = marked \cup Reachable(frontier)

(* ------------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Start"
    /\ TypeOK

(* ------------------------------------------------------------------------- *)
(* Actions                                                                  *)
(* ------------------------------------------------------------------------- *)
Explore ==
    /\ pc = "Start"
    /\ marked' = marked \cup frontier
    /\ frontier' = Succ(frontier) \ (marked \cup frontier)
    /\ pc' = "Explore"
    /\ TypeOK

Done ==
    /\ pc = "Explore"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED << marked, frontier >>
    /\ TypeOK

Next ==
    \/ Explore
    \/ Done

(* ------------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ------------------------------------------------------------------------- *)
(* Invariants and properties                                                *)
(* ------------------------------------------------------------------------- *)
Inv1 == Inv1
Inv2 == Inv2
Inv3 == Inv3

(* ------------------------------------------------------------------------- *)
(* Theorem stating partial correctness                                        *)
(* ------------------------------------------------------------------------- *)
THEOREM PartialCorrectness ==
    Spec => [] (pc = "Done" => marked = Reachable({Root}))

====