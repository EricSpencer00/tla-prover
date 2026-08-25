---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Operator that will replace the generic successor relation Succ in the
   configuration.  Each node has exactly two successors. *)
ConnectedToSomeButNotAll(n) ==
  CASE n = 0 -> {1, 2}
  [] n = 1 -> {2, 3}
  [] n = 2 -> {3, 0}
  [] n = 3 -> {0, 1}
  [] OTHER -> {}

(* A finite version of the Seq operator, limiting sequence length to the
   number of nodes. *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

(* Initial state: only the root is in the frontier, nothing is marked yet,
   and the algorithm is in the running mode. *)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "run"

(* One step of the sequential reachability algorithm. *)
Next ==
  \/ /\ pc = "run"
     /\ LET NewFrontier == { n \in Nodes :
                               \E m \in Frontier : n \in ConnectedToSomeButNotAll[m] }
                           \ (Marked \cup Frontier)
        IN
        /\ Marked'   = Marked \cup Frontier
        /\ Frontier' = NewFrontier
        /\ pc'       = IF NewFrontier = {} THEN "done" ELSE "run"
  \/ /\ pc = "done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

vars == <<Marked, Frontier, pc>>

Spec == Init /\ [][Next]_vars

(* Type correctness invariant *)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

(* Successor‑closure invariant *)
Inv1 ==
  \A n \in Marked :
    ConnectedToSomeButNotAll[n] \subseteq Marked \cup Frontier

(* Disjointness of marked and frontier sets *)
Inv2 ==
  Marked \cap Frontier = {}

(* Definition of the set of nodes reachable from Root using bounded paths *)
Reachable ==
  { n \in Nodes :
        \E p \in LimitedSeq(Nodes) :
           /\ Len(p) >= 1
           /\ p[1] = Root
           /\ p[Len(p)] = n
           /\ \A i \in 1..Len(p)-1 :
                p[i+1] \in ConnectedToSomeButNotAll[p[i]] }

(* Reachable‑set equality invariant *)
Inv3 ==
  Marked \cup Frontier = Reachable

(* Partial correctness: when the algorithm terminates, all reachable nodes
   have been marked. *)
PartialCorrectness ==
  (pc = "done") => (Marked = Reachable)

(* Termination property: eventually the algorithm reaches the completed state. *)
Termination == <> (pc = "done")
====