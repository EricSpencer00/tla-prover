---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

(* Concrete graph: 4 nodes, each with exactly two successors *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root \in Nodes

ConnectedToSomeButNotAll ==
  [n \in Nodes |
    CASE n = 1 -> {2, 3}
    [] n = 2 -> {3, 4}
    [] n = 3 -> {4, 1}
    [] n = 4 -> {1, 2}
    [] OTHER -> {}]

(* Finite sequences of Nodes, length bounded by |Nodes| *)
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

(* Reachable nodes via bounded paths *)
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]] }

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

Next ==
  \/ /\ pc = "init"
     /\ pc' = "step"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "step"
     /\ LET newFront == { m \in Nodes : \E p \in frontier : m \in Succ[p] } IN
        /\ marked'   = marked \cup frontier
        /\ frontier' = newFront \ marked
        /\ pc'       = IF newFront = {} THEN "done" ELSE "step"
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

(* Invariant 1: every frontier node is a successor of some marked node *)
Inv1 ==
  \A n \in frontier : \E p \in marked : n \in Succ[p]

(* Invariant 2: marked set is included in the set of reachable nodes *)
Inv2 ==
  marked \subseteq Reachable

(* Invariant 3: marked ∪ frontier equals the reachable set *)
Inv3 ==
  marked \cup frontier = Reachable

PartialCorrectness ==
  pc = "done" => marked = Reachable

Termination == <> (pc = "done")

====