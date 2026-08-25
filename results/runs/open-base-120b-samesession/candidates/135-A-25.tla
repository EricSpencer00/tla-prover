---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(* Concrete graph with 4 nodes, each having exactly two successors *)
Nodes == {1, 2, 3, 4}
Root  == 1

(* Bounded successor relation used to replace Succ by the .cfg *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = 1 -> {2, 3}
    [] n = 2 -> {3, 4}
    [] n = 3 -> {1, 4}
    [] n = 4 -> {1, 2}
  ]

(* Finite version of Seq, limited by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

(* Initial state *)
Init ==
  /\ marked   = {Root}
  /\ frontier = Succ[Root]
  /\ pc       = "Step"

(* One step of the sequential reachability algorithm *)
Next ==
  \/ /\ pc = "Step"
     /\ frontier # {}
     /\ LET n == CHOOSE x \in frontier IN
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ setminus marked)
          /\ pc'       = "Step"
  \/ /\ pc = "Step"
     /\ frontier = {}
     /\ pc'       = "Done"
     /\ UNCHANGED <<marked, frontier>>

(* Full specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Step", "Done"}

(* Invariant 1: successor closure *)
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Invariant 2: frontier is disjoint from marked and contains only unmarked nodes *)
Inv2 ==
  /\ frontier \cap marked = {}
  /\ frontier \subseteq Nodes \ marked

(* Reachable set defined via bounded sequences *)
ReachableSet ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
  }

(* Invariant 3: marked ∪ frontier equals the set of nodes reachable from Root *)
Inv3 == marked \cup frontier = ReachableSet

(* Partial correctness: when the algorithm terminates, marked equals the reachable set *)
PartialCorrectness == (pc = "Done") => (marked = ReachableSet)

(* Liveness property: the algorithm eventually terminates *)
Termination == <> (pc = "Done")
====