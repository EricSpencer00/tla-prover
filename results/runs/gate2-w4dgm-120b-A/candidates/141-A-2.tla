---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(n) ==
  \/ IF n \notin visited
       THEN /\ visited' = visited \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ visited' = visited
            /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier = {} THEN "done" ELSE pc

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Next)

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  /\ \A x \in visited : Succ[x] \subseteq visited \cup frontier
  /\ Nodes = visited \cup frontier

Inv2 ==
  \A A, B \in SUBSET Nodes :
    (A \cup B = Nodes) => (ReachableFrom(A) \cup ReachableFrom(B) = Nodes)

Inv3 ==
  ReachableFrom({Root}) = visited \cup ReachableFrom(frontier)

PartialCorrectness == visited = ReachableFrom({Root})

Termination == (frontier # {}) ~> (frontier = {})

ConnectedToSomeButNotAll == Succ

LimitedSeq == Seq

====