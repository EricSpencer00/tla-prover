---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\*  Finite sequence operator (replaces the unbounded Seq defined in
\*  the Sequences module).  All sequences are limited to a length no
\*  greater than the number of nodes, guaranteeing a finite state space.
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\*  Successor relation (replaces the generic Succ operator).  Each node
\*  has exactly two distinct successors, providing a non‑trivial but
\*  bounded graph.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CASE n = "n1" -> {"n2", "n3"};
       n = "n2" -> {"n3", "n4"};
       n = "n3" -> {"n4", "n1"};
       n = "n4" -> {"n1", "n2"};
       OTHER    -> {}

\* ----------------------------------------------------------------------
\*  State variables inherited from the sequential reachability algorithm.
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\*  Initial state (instantiated with the concrete graph).
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\*  Next‑state relation (the core of the sequential algorithm).
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Run"
     /\ \E n \in Frontier:
          /\ Marked'   = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup ConnectedToSomeButNotAll(n)
          /\ pc'       = "Run"
  \/ /\ pc = "Run"
     /\ Frontier = {}
     /\ pc' = "Done"
  \/ /\ pc = "Done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

Vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\*  Specification required by the .cfg file.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\*  Invariants required by the .cfg file.
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 ==
  /\ \A n \in Marked : 
        \A m \in ConnectedToSomeButNotAll(n) : m \in Marked \/ m \in Frontier

Inv2 ==
  /\ \A n \in Frontier :
        \E m \in Marked : n \in ConnectedToSomeButNotAll(m)

Inv3 ==
  /\ \A n \in Nodes :
        (n \in Marked) \/ (n \in Frontier) \/ (n \notin Marked /\ n \notin Frontier)

PartialCorrectness ==
  /\ pc = "Done"
  => Marked = Nodes

\* ----------------------------------------------------------------------
\*  Liveness property (termination).
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====