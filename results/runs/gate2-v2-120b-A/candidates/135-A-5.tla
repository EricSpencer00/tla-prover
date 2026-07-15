---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

(* -----------------------------------------------------------------
   Constants required by the reference configuration
   ----------------------------------------------------------------- *)
CONSTANTS
    Nodes,   \* The finite set of node identifiers
    Root,    \* The distinguished start node
    Succ,    \* Function mapping each node to a non‑empty set of its successors
    Seq      \* Sequence type used for paths (will be overridden by the CFG)

(* -----------------------------------------------------------------
   Derived definitions
   ----------------------------------------------------------------- *)
Node == Nodes

(* -----------------------------------------------------------------
   State variables (inherited from the sequential reachability algorithm)
   ----------------------------------------------------------------- *)
VARIABLES
    marked,   \* Set of nodes known to be reachable
    frontier, \* Set of nodes whose successors are yet to be explored
    pc        \* Program counter of the single process (one of "Init", "Step", "Done")

(* -----------------------------------------------------------------
   Initial state (inherits semantics from the algorithm)
   ----------------------------------------------------------------- *)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Step"

(* -----------------------------------------------------------------
   Next-state relation (single sequential process)
   ----------------------------------------------------------------- *)
Step ==
    /\ pc = "Step"
    /\ \E n \in frontier :
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
    /\ pc' = IF frontier' = {} THEN "Done" ELSE "Step"

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == Step \/ Done

(* -----------------------------------------------------------------
   Specification
   ----------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* -----------------------------------------------------------------
   Safety invariants required by the configuration
   ----------------------------------------------------------------- *)

(* Type correctness: all state variables range over appropriate domains *)
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Step", "Done"}

(* Inv1: Successor closure – every node in the frontier has all its
   successors either already marked or in the frontier. *)
Inv1 ==
    \A n \in frontier : Succ[n] \subseteq marked \cup frontier

(* Inv2: Reachability decomposition – the union of marked and frontier
   is exactly the set of nodes reachable from the root via paths bounded
   by the number of nodes. *)
Inv2 ==
    marked \cup frontier = { n \in Nodes : \E p \in Seq :
        Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = n /\
        \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]] }

(* Inv3: Reachable set equality – the set of nodes reachable from the root
   (as defined by the existential path quantifier) equals the set of marked nodes. *)
Inv3 ==
    marked = { n \in Nodes : \E p \in Seq :
        Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = n /\
        \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]] }

(* PartialCorrectness – when the algorithm terminates, all nodes reachable
   from the root are exactly those in the marked set. *)
PartialCorrectness ==
    pc = "Done" => marked = { n \in Nodes : \E p \in Seq :
        Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = n /\
        \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]] }

(* -----------------------------------------------------------------
   Liveness property – termination eventually reached
   ----------------------------------------------------------------- *)
Termination == <> (pc = "Done")

=============================================================================