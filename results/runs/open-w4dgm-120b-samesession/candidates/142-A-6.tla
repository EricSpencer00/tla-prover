---- MODULE ReachableProofs ----
EXTENDS ReachableAlgo, ReachableLemmas, Integers

CONSTANTS Nodes, Root

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

StartStep ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "working"
  /\ UNCHANGED <<marked, frontier>>

MarkNode(x) ==
  /\ pc = "working"
  /\ x \in frontier
  /\ marked' = marked \cup {x}
  /\ frontier' = frontier \ {x}
  /\ UNCHANGED <<pc>>

ActivateSuccessor(y) ==
  /\ pc = "working"
  /\ \E x \in marked :
       /\ y \in Succ(x)
       /\ y \notin marked
       /\ y \notin frontier
  /\ frontier' = frontier \cup {y}
  /\ UNCHANGED <<marked, pc>>

HaltStep ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "idle"
  /\ UNCHANGED <<marked, frontier>>

AllDone ==
  /\ pc = "idle"
  /\ frontier = {}
  /\ marked = Nodes
  /\ UNCHANGED <<marked, frontier, pc>>

StepBound == 2 * Cardinality(Nodes)
Step ==
  \/ StartStep
  \/ \E x \in Nodes : MarkNode(x)
  \/ \E y \in Nodes : ActivateSuccessor(y)
  \/ HaltStep
  \/ AllDone

Reachable == {{Root}} \cup (Succ @@ {{Root}})

Spec == Init /\ [][Step]_<<marked, frontier, pc>>

Invariant1 ==
  /\ TypeOK
  /\ \A x \in marked : Succ(x) \subseteq (marked \cup frontier)

Invariant2 == reachable(Reachable) = reachable(marked \cup frontier)

Invariant3 == reachable({Root}) = marked \cup reachable(frontier)

Terminate == pc = "idle" /\ frontier = {} /\ marked = Nodes

Theorem Terminate => (marked = reachable({Root}))
====