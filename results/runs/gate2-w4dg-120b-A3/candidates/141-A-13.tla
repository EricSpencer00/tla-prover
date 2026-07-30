---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

ProcessStep ==
  \/ (\E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ UNCHANGED pc)
  \/ (\E n \in frontier :
        /\ n \in marked
        /\ frontier' = frontier \ {n}
        /\ UNCHANGED <<marked, pc>>)

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ ProcessStep
  \/ Terminate

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in Nodes : (n \in marked) => (Succ[n] \subseteq marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup (ReachableFromSet(Nodes, frontier))
    = ReachableFromSet(Nodes, marked \cup frontier)

Inv3 ==
  ReachableFromSet(Nodes, {Root}) = marked \cup ReachableFromSet(Nodes, frontier)

PartialCorrectness ==
  \A n \in Nodes :
    (pc = "done") => (n \in marked <=> ReachableFromSet(Nodes, {Root})[n])

Termination ==
  (Cardinality(ReachableFromSet(Nodes, {Root})) < \infinity)
    ~> (pc = "done")

LimitedSeq == Seq
ConnectedToSomeButNotAll == Succ
====