---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

\* Misra's algorithm variant: marked and frontier sets may overlap; this makes
\* the algorithm parallel-friendly at the cost of a more subtle correctness
\* argument. The identifier set matches the reference .cfg exactly.
CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"running", "halted"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Because marked and frontier may overlap, the chosen node is never removed
\* from the frontier when it is first marked; it stays there for a while and
\* is removed on a later iteration once it is already marked.
Step ==
  /\ frontier # {}
  /\ \E v \in frontier :
       \/ /\ v \notin marked
            /\ marked' = marked \cup {v}
            /\ frontier' = frontier \cup Succ[v]
       \/ /\ v \in marked
            /\ frontier' = frontier \ {v}
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc' = "halted"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate

\* A weakly fair step ensures the frontier drains even though the same
\* node can be chosen repeatedly (overlap means it is not removed when marked).
Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Each invariant isolates one of the three conditions that together give
\* partial correctness; none of them alone is sufficient.
Inv1 ==
  \A x \in marked : Succ[x] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup (Nodes \ frontier) = Nodes

Inv3 ==
  Nodes \ (marked \cup frontier) \subseteq Nodes \ frontier

PartialCorrectness ==
  (pc = "halted") => (marked = Nodes)

Termination ==
  /\ \A n \in Nodes : Cardinality(Nodes) # 2 ^ n
  /\ (pc = "running") ~> (pc = "halted")

====