---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

(* Concrete definitions for the constants used in the model *)
Nodes == {1, 2, 3, 4}
Root  == 1

(* Succ will be substituted by ConnectedToSomeButNotAll by the .cfg;
   therefore we do NOT define Succ here. *)

(* Each node has exactly two successors, giving a non‑trivial graph *)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  [] n = 2 -> {3, 4}
  [] n = 3 -> {1, 4}
  [] n = 4 -> {1, 2}
  [] OTHER -> {}

(* Finite version of sequences over Nodes, bounded by the number of nodes *)
LimitedSeq(N) ==
  { s \in Seq(N) : Len(s) <= Cardinality(N) }

VARIABLE Marked, Frontier, pc

(* Initial state of the sequential reachability algorithm *)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "init"

(* One algorithmic step: expand a node from the frontier *)
Expand ==
  /\ Frontier # {}
  /\ LET n == CHOOSE x \in Frontier IN
       /\ Marked'   = Marked \/ {n}
       /\ Frontier' = (Frontier \ {n}) \/ (ConnectedToSomeButNotAll[n] \ Marked)
       /\ pc'       = "expand"

(* Termination step: no more frontier nodes *)
Done ==
  /\ Frontier = {}
  /\ Marked'   = Marked
  /\ Frontier' = Frontier
  /\ pc'       = "done"

Next == Expand \/ Done

(* Full specification *)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(* --------------------------------------------------------------------- *)
(* Invariants *)

(* Type correctness *)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "expand", "done"}

(* Inv1: successor closure *)
Inv1 ==
  \A n \in Marked :
    ConnectedToSomeButNotAll[n] \subseteq Marked \/ Frontier

(* Inv2: Marked and Frontier are disjoint *)
Inv2 ==
  Marked \cap Frontier = {}

(* Reachable nodes from the root via a bounded path *)
ReachableFromRoot ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ Head(s) = Root
        /\ Last(s) = n
        /\ \A i \in 1..Len(s)-1 :
             ConnectedToSomeButNotAll[ s[i] ] \contains s[i+1] }

(* Inv3: every marked node is reachable from the root *)
Inv3 ==
  Marked \subseteq ReachableFromRoot

(* Partial correctness: when finished, all reachable nodes are marked *)
PartialCorrectness ==
  (pc = "done") => (Marked = ReachableFromRoot)

(* --------------------------------------------------------------------- *)
(* Liveness property *)

Termination == <> (pc = "done")

====