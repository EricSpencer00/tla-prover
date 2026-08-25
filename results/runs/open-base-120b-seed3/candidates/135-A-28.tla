---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------
  Concrete assumptions for model checking (4 nodes, each with 2 successors)
--------------------------------------------------------------------*)
ASSUME /\ Nodes = {1, 2, 3, 4}
       /\ Root \in Nodes
       /\ Succ \in [Nodes -> SUBSET Nodes]
       /\ \A n \in Nodes: Cardinality(Succ[n]) = 2
       /\ \A n \in Nodes: Succ[n] \subseteq Nodes

(*--------------------------------------------------------------------
  Operator that the .cfg substitutes for Succ
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll == Succ

(*--------------------------------------------------------------------
  Finite version of Seq over Nodes (bounded by |Nodes|)
--------------------------------------------------------------------*)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(*--------------------------------------------------------------------
  One step of the sequential reachability algorithm
--------------------------------------------------------------------*)
Next ==
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ \E n \in frontier:
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ (marked \cup {n}))
            /\ pc' = "run"
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ marked' = marked
       /\ frontier' = frontier
       /\ pc' = "done"

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Reachability definition using the bounded sequence operator
--------------------------------------------------------------------*)
Reachable(root) ==
    { n \in Nodes :
        \E s \in LimitedSeq :
            /\ Len(s) > 0
            /\ s[1] = root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
    }

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 == \A n \in marked : Succ[n] \subseteq marked \/ frontier

Inv2 == marked \cap frontier = {}

Inv3 == marked \cup frontier \subseteq Reachable(Root)

PartialCorrectness == (pc = "done") => (marked = Reachable(Root))

(*--------------------------------------------------------------------
  Liveness property (termination)
--------------------------------------------------------------------*)
Termination == <> (pc = "done")

====