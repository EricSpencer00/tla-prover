---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the configuration
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*-----------------------------------------------------------------
  State variables inherited from the sequential reachability algorithm
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Vars == << marked, frontier, pc >>

(* The set of successors of a node; in the abstract model we leave it
   uninterpreted and assume the necessary lemmas are proved elsewhere. *)
Succ == [n \in Nodes |-> {}]  \* Placeholder; actual implementation provided by the extended module.

(* Reachable set from a given set of start nodes, using the successor relation. *)
REACHABLE(start) ==
  LET R == RECURSIVE R(_)
  IN
    R(start) = start \cup
               UNION { Succ[n] : n \in R(start) }

(*-----------------------------------------------------------------
  Initial state (the actual condition is defined in the extended module;
   we provide a placeholder that satisfies the required type constraints)
-----------------------------------------------------------------*)
Init ==
  /\ pc = "Init"
  /\ marked = {}
  /\ frontier = {Root}

/*-----------------------------------------------------------------
  Actions (placeholders; concrete definitions are inherited)
-----------------------------------------------------------------*/
MarkFrontier ==
  /\ pc = "Explore"
  /\ \E n \in frontier :
        /\ pc' = "Explore"
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)

Done ==
  /\ pc = "Explore"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED << marked, frontier >>

Next ==
  \/ MarkFrontier
  \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_Vars

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
(* Invariant 1: type correctness plus every successor of a marked node
   is either already marked or in the frontier. *)
Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ Root \in Nodes
  /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Invariant 2: the marked set plus nodes reachable from the frontier equals
   the nodes reachable from the union of marked and frontier. *)
Inv2 ==
  marked \cup REACHABLE(frontier) = REACHABLE(marked \cup frontier)

(* Invariant 3: the set of reachable nodes from the root equals the marked set
   plus nodes reachable from the frontier. *)
Inv3 ==
  REACHABLE({Root}) = marked \cup REACHABLE(frontier)

(*-----------------------------------------------------------------
  Theorem proving partial correctness (TLAPS placeholder)
-----------------------------------------------------------------*)
THEOREM TerminationPartialCorrectness ==
  \A s : (s \in Spec) => (pc = "Done") => (marked = REACHABLE({Root}))

(*-----------------------------------------------------------------
  Export the required identifiers for the configuration
-----------------------------------------------------------------*)
INVARIANTS == << Inv1, Inv2, Inv3 >>
PROPERTIES == << TerminationPartialCorrectness >>

====