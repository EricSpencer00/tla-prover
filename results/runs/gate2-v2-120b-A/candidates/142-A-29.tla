---- MODULE ReachableProofs ----
EXTENDS TLC

(* ----------------------------------------------------------------------
   Constants required by the specification (as listed in the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS Nodes, Root

(* ----------------------------------------------------------------------
   State variables: 
     - marked : set of nodes that have been discovered
     - frontier : set of nodes that are discovered but whose successors 
                  have not yet been explored
     - pc : program counter indicating the current phase of the algorithm
   ---------------------------------------------------------------------- *)
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
   Helper definition for the set of successors of a node.
   The actual graph is assumed to be a constant function Succ that maps
   each node to the set of its immediate successors.  For the purpose of
   this module we leave Succ uninterpreted; the .cfg file must supply a
   mapping for it.
   ---------------------------------------------------------------------- *)
Succ == [n \in Nodes |-> {}]

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Explore"

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)
Explore ==
    /\ pc = "Explore"
    /\ frontier # {}
    /\ LET n == CHOOSE x \in frontier : TRUE IN
       /\ marked'   = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
       /\ pc'       = "Explore"
    /\ UNCHANGED << >>

Terminate ==
    /\ pc = "Explore"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED << marked, frontier >>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next == Explore \/ Terminate

(* ----------------------------------------------------------------------
   Specification (the overall behavior of the system)
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Invariant 1: type correctness and that every successor of a marked node
               is either already marked or in the frontier.
   ---------------------------------------------------------------------- *)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ marked \cup frontier \subseteq Nodes
    /\ \A n \in marked : (Succ[n] \subseteq marked) \/ (Succ[n] \subseteq frontier)

(* ----------------------------------------------------------------------
   Invariant 2: the set of nodes reachable from the union of marked and
               frontier equals the union of marked and the nodes reachable
               from the frontier.
   ---------------------------------------------------------------------- *)
ReachFrom(S) == 
    \* The set of nodes reachable from a set S via zero or more successor steps.
    CHOOSE R \in SUBSET Nodes : 
       (S \subseteq R) /\ 
       (\A n \in R : Succ[n] \subseteq R) /\ 
       (\A R2 \in SUBSET Nodes :
          (S \subseteq R2) /\ (\A n \in R2 : Succ[n] \subseteq R2) => R \subseteq R2)

Inv2 ==
    ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)

(* ----------------------------------------------------------------------
   Invariant 3: the set of nodes reachable from the root equals the marked
               set plus the nodes reachable from the frontier.
   ---------------------------------------------------------------------- *)
Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

(* ----------------------------------------------------------------------
   Theorem stating partial correctness: when the algorithm terminates,
   the marked set equals the set of nodes reachable from the root.
   ---------------------------------------------------------------------- *)
THEOREM PartialCorrectness ==
    Spec => [](pc = "Done" => marked = ReachFrom({Root}))

(* ----------------------------------------------------------------------
   Exported identifiers required by the .cfg file
   ---------------------------------------------------------------------- *)
SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANT Inv1
INVARIANT Inv2
INVARIANT Inv3
PROPERTIES PartialCorrectness

====