---- MODULE Reachable ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier:
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Explore)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  ReachableFrom(frontier) \cup marked = ReachableFrom(marked \cup frontier)

\* ReachableFrom is defined below, so the invariant may refer to it.
Inv3 ==
  ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

\* ReachableFrom is a standard reachability closure on the Succ map.
ReachableFrom(S) ==
  LET step(T) == T \cup {y \in Nodes : \E x \in T : y \in Succ[x]}
  IN  CHOOSE N \in {N \in [1..Seq -> SUBSET Nodes] :
                      T == step[#1] /\ (\A k \in 1..(#1 - 1) : T == step[#k])
                      /\ #1 = Seq} : TRUE

PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom({Root}))

Termination ==
  /\ \A n \in Nodes : Cardinality(ReachableFrom({n})) < Seq
  /\ ~(\E n \in frontier : n \in marked)
  /\ TRUE

====