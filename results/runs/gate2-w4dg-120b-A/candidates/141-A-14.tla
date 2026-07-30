---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

ReachableSet(X) ==
  { n \in Nodes : \E k \in 1 .. Seq : \E f \in [1 .. k -> X] : f[k] = n }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Step ==
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)
        /\ WF_vars(Terminate)

Inv1 ==
  \A n \in Nodes :
    n \in marked => (Succ[n] \subseteq (marked \cup frontier))

Inv2 ==
  (marked \cup frontier) = ReachableSet(marked \cup frontier)
    => (marked \cup ReachableSet(frontier)) = ReachableSet(marked \cup frontier)

Inv3 ==
  ReachableSet({Root}) = marked \cup ReachableSet(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachableSet({Root}))

Termination ==
  (ReachableSet(Nodes) # {}) ~> (pc = "done")

====