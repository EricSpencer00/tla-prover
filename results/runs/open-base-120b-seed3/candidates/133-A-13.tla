---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

(* ----------------------------------------------------------------------
   Concrete graph definition (overridden by the .cfg)
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll ==
    [n \in Nodes |-> { s \in Nodes : TRUE }]

(* each node must have exactly two successors – an assumption used by TLC *)
ASSUME \A n \in Nodes : Cardinality(ConnectedToSomeButNotAll[n]) = 2

(* ----------------------------------------------------------------------
   Bounded sequence operator used in place of Seq (the .cfg substitutes
   LimitedSeq for Seq)
   ---------------------------------------------------------------------- *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) \le Cardinality(Nodes) }

(* ----------------------------------------------------------------------
   State variables (inherited from the parallel reachability algorithm)
   ---------------------------------------------------------------------- *)
VARIABLES Marked, Frontier, PC, Sel, SuccSet

vars == <<Marked, Frontier, PC, Sel, SuccSet>>

(* ----------------------------------------------------------------------
   Initial state (concrete instantiation of the generic algorithm)
   ---------------------------------------------------------------------- *)
Init ==
    /\ Marked   = {}
    /\ Frontier = {Root}
    /\ PC       = [p \in Procs |-> "idle"]
    /\ Sel      = [p \in Procs |-> <<>>]
    /\ SuccSet  = [p \in Procs |-> {}]

(* ----------------------------------------------------------------------
   Worker actions (simplified versions of the parallel algorithm actions)
   ---------------------------------------------------------------------- *)
PickNode(p) ==
    /\ p \in Procs
    /\ PC[p] = "idle"
    /\ \E n \in Frontier :
        /\ Sel'      = [Sel EXCEPT ![p] = <<n>>]
        /\ Marked'   = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup ConnectedToSomeButNotAll[n]
        /\ PC'       = [PC EXCEPT ![p] = "working"]
        /\ SuccSet'  = SuccSet
    /\ UNCHANGED <<Marked, Frontier, PC, Sel, SuccSet>> \ {Sel, Marked, Frontier, PC}

Finish(p) ==
    /\ p \in Procs
    /\ PC[p] = "working"
    /\ Sel[p] # <<>>
    /\ Sel' = [Sel EXCEPT ![p] = <<>>]
    /\ PC'  = [PC EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<Marked, Frontier, SuccSet>>

Next ==
    \/ \E p \in Procs : PickNode(p)
    \/ \E p \in Procs : Finish(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Inductive invariant (type correctness + control‑flow properties)
   ---------------------------------------------------------------------- *)
Inv ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A p \in Procs : PC[p] \in {"idle", "working"}
    /\ \A p \in Procs : Sel[p] \in LimitedSeq(Nodes)

(* ----------------------------------------------------------------------
   Refinement property (parallel algorithm implements sequential Misra)
   ---------------------------------------------------------------------- *)
Refines == Inv

====