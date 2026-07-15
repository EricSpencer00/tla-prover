---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes,   \* Set of all graph nodes
    Root,    \* Starting node (must be in Nodes)
    Succ,    \* Successor function: [Nodes -> SUBSET Nodes]
    Seq      \* Not used directly in the spec but required by .cfg

VARIABLES
    marked,      \* Set of visited (marked) nodes
    frontier,    \* Set of nodes awaiting exploration (may overlap with marked)
    pc           \* Program counter: "Loop" or "Done"

(* ------------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"Loop", "Done"}

(* ------------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"
    /\ TypeOK

(* ------------------------------------------------------------------------- *)
(* Main action with two nondeterministic cases *)
Next ==
    /\ pc = "Loop"
    /\ frontier # {}                                   \* there is at least one node to pick
    /\ \E n \in frontier :
          \/ /\ n \notin marked
                /\ marked'   = marked \cup {n}
                /\ frontier' = frontier \cup Succ[n]
                /\ pc'       = "Loop"
          \/ /\ n \in marked
                /\ marked'   = marked
                /\ frontier' = frontier \ {n}
                /\ pc'       = "Loop"
    /\ UNCHANGED << >>                                   \* no other variables change

(* Termination transition *)
Terminate ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

NextStep == Next \/ Terminate

(* ------------------------------------------------------------------------- *)
(* Specification *)
Spec ==
    Init /\ [][NextStep]_<<marked, frontier, pc>>

(* ------------------------------------------------------------------------- *)
(* Safety invariants derived from the description *)

(* 1. Every successor of a marked node is either marked or in the frontier *)
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* 2. The union of marked and nodes reachable from frontier equals the nodes reachable from the union of marked and frontier *)
(* Helper: reachable from a set of seeds *)
ReachFrom(S) ==
    LET R == { n \in Nodes : \E s \in S : s \in ReachableFromRootVia[s] } IN R

(* Since we cannot define ReachableFromRootVia directly without recursion,
   we use a least fixed point definition via the built‑in RECURSIVE construct. *)

RECURSIVE ReachableFromRootVia(_)
ReachableFromRootVia(s) ==
    { s } \cup UNION { ReachableFromRootVia(t) : t \in Succ[s] }

Inv2 ==
    (marked \cup { n \in Nodes : \E f \in frontier : n \in ReachableFromRootVia[f] })
      =
    { n \in Nodes : \E s \in (marked \cup frontier) : n \in ReachableFromRootVia[s] }

(* 3. Reachable from Root equals marked plus nodes reachable from frontier *)
Inv3 ==
    { n \in Nodes : n \in ReachableFromRootVia[Root] } =
    marked \cup { n \in Nodes : \E f \in frontier : n \in ReachableFromRootVia[f] }

(* Partial correctness: when terminated, marked equals the set of nodes reachable from Root *)
PartialCorrectness ==
    pc = "Done" => 
        marked = { n \in Nodes : n \in ReachableFromRootVia[Root] }

(* ------------------------------------------------------------------------- *)
(* Liveness property: termination (for finite reachable set) will be expressed in the .cfg *)

THEOREM Spec => []PartialCorrectness

====