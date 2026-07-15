---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* ----------------------------------------------------------------------
   Constants (to be instantiated in the .cfg)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Nodes,   \* Set of graph nodes
    Root,    \* The distinguished start node
    Procs,   \* Set of worker process identifiers
    Succ,    \* Function mapping each node to a two‑element set of its successors
    Seq      \* Upper bound on the length of per‑process sequences

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
NodeSeq == Seq(0 .. Seq)

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    marked,      \* Set of nodes already reached
    frontier,    \* Set of nodes currently pending exploration
    pc,          \* Mapping from each process to its program counter
    sel,         \* Mapping from each process to the node it currently selects (or NULL)
    succSet      \* Mapping from each process to the set of successors of its selected node (or {})
    
\* Helper: a distinguished value meaning “no node selected”
NULL == -1

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = [p \in Procs |-> "Idle"]
    /\ sel      = [p \in Procs |-> NULL]
    /\ succSet  = [p \in Procs |-> {}]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

SelectNode(p) ==
    /\ pc[p] = "Idle"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ sel'      = [sel EXCEPT ![p] = n]
          /\ frontier' = frontier \ {n}
          /\ marked'   = marked \cup {n}
          /\ succSet'  = [succSet EXCEPT ![p] = Succ[n]]
          /\ pc'       = [pc EXCEPT ![p] = "ProcessSucc"]
    /\ UNCHANGED <<marked, frontier>>

ProcessSucc(p) ==
    /\ pc[p] = "ProcessSucc"
    /\ \E n \in succSet[p] :
          /\ frontier' = frontier \cup {n}
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<marked, frontier, sel, succSet>>

Next ==
    \/ \E p \in Procs : SelectNode(p)
    \/ \E p \in Procs : ProcessSucc(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(* ----------------------------------------------------------------------
   Safety invariant (type‑correctness + control‑flow)
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc       \in [Procs -> {"Idle", "ProcessSucc"}]
    /\ \A p \in Procs :
          (pc[p] = "Idle") =>
              /\ sel[p] \in Nodes \/ sel[p] = NULL
              /\ succSet[p] = {}
          (pc[p] = "ProcessSucc") =>
              /\ sel[p] \in Nodes
              /\ succSet[p] = Succ[sel[p]]
    /\ \A p \in Procs :
          sel[p] = NULL => succSet[p] = {}
    /\ frontier = Nodes \ marked

Inv == TypeOK

(* ----------------------------------------------------------------------
   Refinement property (parallel algorithm implements sequential Misra)
   ---------------------------------------------------------------------- *)

SeqReachable == { n \in Nodes :
                    \E s \in NodeSeq :
                       /\ Len(s) <= Seq
                       /\ s[1] = Root
                       /\ \A i \in 1 .. Len(s)-1 : s[i+1] \in Succ[s[i]]
                       /\ n \in { s[i] : i \in 1 .. Len(s) } }

Refines == marked \subseteq SeqReachable

=============================================================================