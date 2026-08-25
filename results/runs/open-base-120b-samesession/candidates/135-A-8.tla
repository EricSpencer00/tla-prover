---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* ----------------------------------------------------------------------
   Concrete configuration for model checking
   ---------------------------------------------------------------------- *)

(* the set of nodes (4 nodes) *)
ASSUME Nodes = {"n1", "n2", "n3", "n4"}

(* the distinguished start node *)
ASSUME Root \in Nodes

(* each node has exactly two successors – this operator substitutes for Succ *)
ConnectedToSomeButNotAll == 
  [n \in Nodes |-> 
    CASE n = "n1" -> {"n2", "n3"}
    [] n = "n2" -> {"n1", "n4"}
    [] n = "n3" -> {"n1", "n4"}
    [] n = "n4" -> {"n2", "n3"}]

(* bounded version of Seq – needed for a finite state space *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ----------------------------------------------------------------------
   Variables of the sequential reachability algorithm
   ---------------------------------------------------------------------- *)

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

(* ----------------------------------------------------------------------
   Transition relation (the algorithm)
   ---------------------------------------------------------------------- *)

Next ==
  \/ /\ pc # "done"
     /\ frontier # {}
     /\ \E n \in frontier:
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked)
          /\ pc'       = "run"
  \/ /\ pc # "done"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "run", "done"}

(* ----------------------------------------------------------------------
   Algorithm invariants
   ---------------------------------------------------------------------- *)

(* Inv1: all successors of already marked nodes are either marked or pending *)
Inv1 ==
  \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

(* helper: existence of a bounded path from Root to a node *)
Path(n) ==
  \E s \in LimitedSeq(Nodes) :
    /\ Len(s) >= 1
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1..(Len(s)-1) : s[i+1] \in ConnectedToSomeButNotAll[s[i]]

(* Inv2: every node that is reachable by a bounded path is already marked *)
Inv2 ==
  \A n \in Nodes : (Path(n) => n \in marked)

(* Inv3: the set of marked nodes equals the set of nodes reachable via a bounded path *)
Inv3 ==
  marked = { n \in Nodes : Path(n) }

(* ----------------------------------------------------------------------
   Partial correctness – when the algorithm finishes, it has discovered
   exactly the reachable nodes.
   ---------------------------------------------------------------------- *)

PartialCorrectness ==
  /\ pc = "done"
  => marked = { n \in Nodes : Path(n) }

(* ----------------------------------------------------------------------
   Liveness property: termination
   ---------------------------------------------------------------------- *)

Termination == <> (pc = "done")
=============================================================================