---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
(* The successor relation of the graph. *)
Succ == [n \in Nodes |-> {}]  \* Placeholder; actual successors are provided in the .cfg

(* Reachable nodes from a set S of nodes using Succ *)
REACH(S) == 
  LET
    R == [R \in SUBSET Nodes |-> FALSE]
  IN
  UNION { T \in SUBSET Nodes :
           /\ T = {}
           \/ (\E x \in T : 
                 /\ x \in S
                 /\ \E y \in T : y \in Succ[x])
         }

(*--------------------------------------------------------------------
  Type correctness
--------------------------------------------------------------------*)
TypeOK == 
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Init", "Run", "Done"}

(* Invariant 1: type correctness + every successor of a marked node is in marked or frontier *)
Inv1 == 
  /\ TypeOK
  /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Invariant 2: marked ∪ reachable(frontier) = reachable(marked ∪ frontier) *)
Inv2 == 
  marked \cup REACH(frontier) = REACH(marked \cup frontier)

(* Invariant 3: reachable from Root equals marked ∪ reachable(frontier) *)
Inv3 == 
  REACH({Root}) = marked \cup REACH(frontier)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = "Init"
  /\ TypeOK

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Step ==
  \/ /\ pc = "Init"
     /\ pc' = "Run"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "Run"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
          /\ marked'   = marked \cup {n}
          /\ pc'       = "Run"
          /\ TypeOK
  \/ /\ pc = "Run"
     /\ frontier = {}
     /\ marked' = marked
     /\ frontier' = frontier
     /\ pc' = "Done"
  \/ /\ pc = "Done"
     /\ UNCHANGED <<marked, frontier, pc>>

Next == Step

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Theorem (partial correctness): when the algorithm terminates,
  the marked set equals the set of reachable nodes from the root.
--------------------------------------------------------------------*)
THEOREM TerminationImpliesCorrectness ==
  \A s : (s["pc"] = "Done") => (s["marked"] = REACH({Root}))

(*--------------------------------------------------------------------
  Configuration for TLC (normally placed in a .cfg file, but
  provided here as comments for completeness)
--------------------------------------------------------------------*)
(* 
CONSTANTS
  Nodes = {1,2,3,4}
  Root  = 1

INIT Init
NEXT Next
INVARIANT Inv1
INVARIANT Inv2
INVARIANT Inv3
PROPERTIES TerminationImpliesCorrectness
*)

====