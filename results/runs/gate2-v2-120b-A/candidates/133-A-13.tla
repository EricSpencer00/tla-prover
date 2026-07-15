---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Configuration constants (instantiated in the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS Nodes, Root, Procs, Succ, Seq

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
Node == Nodes
Proc == Procs

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    marked,        \* Shared set of marked nodes
    frontier,      \* Shared set of frontier nodes
    pc,            \* Per-process program counter
    sel,           \* Per-process selected node
    succSet        \* Per-process set of successors of the selected node

(* ----------------------------------------------------------------------
   Initialization (example, can be adjusted to match the underlying spec)
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Proc |-> "Start"]
    /\ sel = [p \in Proc |-> NULL]
    /\ succSet = [p \in Proc |-> {}]

(* ----------------------------------------------------------------------
   Actions (place‑holders – the real parallel algorithm would define
   concrete steps; here we provide generic actions that respect the
   description that they are inherited unchanged)
   ---------------------------------------------------------------------- *)

(* Worker p selects a node from the frontier *)
Select(p) ==
    /\ p \in Proc
    /\ frontier # {}
    /\ LET n == CHOOSE x \in frontier : TRUE IN
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
       /\ pc' = [pc EXCEPT ![p] = "Compute"]
       /\ succSet' = succSet
       /\ marked' = marked

(* Worker p computes successors of its selected node *)
Compute(p) ==
    /\ pc[p] = "Compute"
    /\ succSet' = [succSet EXCEPT ![p] = Succ[sel[p]]]
    /\ pc' = [pc EXCEPT ![p] = "Update"]
    /\ UNCHANGED <<marked, frontier, sel>>

(* Worker p updates the shared marked set and frontier *)
Update(p) ==
    /\ pc[p] = "Update"
    /\ marked' = marked \cup {sel[p]}
    /\ frontier' = frontier \cup succSet[p]
    /\ pc' = [pc EXCEPT ![p] = "Start"]
    /\ UNCHANGED <<sel, succSet>>

(* Stuttering step to allow termination *)
Terminate ==
    /\ frontier = {}
    /\ UNCHANGED <<marked, frontier, pc, sel, succSet>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in Proc : Select(p)
    \/ \E p \in Proc : Compute(p)
    \/ \E p \in Proc : Update(p)
    \/ Terminate

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(* ----------------------------------------------------------------------
   Invariant (type correctness and control‑flow properties)
   ---------------------------------------------------------------------- *)
Inv ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ \A p \in Proc :
          /\ sel[p] \in Node \cup {NULL}
          /\ succSet[p] \subseteq Node
          /\ pc[p] \in {"Start", "Compute", "Update"}
    /\ \A p \in Proc :
          IF pc[p] = "Start" THEN sel[p] = NULL
          ELSE IF pc[p] = "Compute" THEN sel[p] # NULL /\ succSet[p] = {}
          ELSE pc[p] = "Update"

(* ----------------------------------------------------------------------
   Refinement property (the parallel algorithm implements the sequential
   Misra algorithm). For illustration we assert that every node eventually
   reaches the same mark as in a hypothetical sequential execution.
   ---------------------------------------------------------------------- *)
Refines ==
    \A n \in Node :
        (n \in marked) => (n \in Seq)    \* placeholder relation

(* ----------------------------------------------------------------------
   THEOREM (optional, but helps TLC)
   ---------------------------------------------------------------------- *)
THEOREM Spec => []Inv

====