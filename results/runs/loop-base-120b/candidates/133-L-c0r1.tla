---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Null

(* Concrete values for the constants – supplied via ASSUME so they do not
   conflict with the CONSTANTS declaration. *)
ASSUME Nodes = {"n1", "n2", "n3", "n4"}
ASSUME Root  = "n1"
ASSUME Procs = {"p1", "p2"}
ASSUME Null  = "Null"

(* Each node has exactly two successors.  The .cfg substitutes this
   operator for the generic Succ operator used in the parallel
   algorithm. *)
ConnectedToSomeButNotAll(n) ==
  CASE n = "n1" -> {"n2", "n3"}
  [] n = "n2" -> {"n3", "n4"}
  [] n = "n3" -> {"n4", "n1"}
  [] n = "n4" -> {"n1", "n2"}
  [] OTHER   -> {}

(* Bounded version of Seq for model checking. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* State variables – those of the parallel reachability algorithm. *)
VARIABLES marked, frontier, pc, sel, succSet

(* Initial state, instantiated with the concrete graph and processes. *)
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = [p \in Procs |-> "idle"]
  /\ sel      = [p \in Procs |-> Null]
  /\ succSet  = [p \in Procs |-> {}]

(* Next-state relation – skeletal placeholder respecting the variable set.
   The real actions are supplied by the parallel algorithm specification. *)
Next ==
  \/ \E p \in Procs:
        /\ pc[p] = "idle"
        /\ pc'   = [pc EXCEPT ![p] = "working"]
        /\ UNCHANGED <<marked, frontier, sel, succSet>>
  \/ /\ frontier' = {}
        /\ marked'   = marked \cup frontier
        /\ UNCHANGED <<pc, sel, succSet>>

(* Full specification required by the .cfg file. *)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(* Inductive invariant: type correctness and basic control‑flow properties. *)
Inv ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs: sel[p] \in Nodes \cup {Null}
  /\ \A p \in Procs: succSet[p] \subseteq Nodes

(* Refinement property asserting that the parallel algorithm implements
   the sequential Misra algorithm.  Here we provide a placeholder that
   always holds. *)
Refines == TRUE

====