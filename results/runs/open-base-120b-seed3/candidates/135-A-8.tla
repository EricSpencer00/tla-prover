---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

\* Concrete instantiation of the constants for model checking
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root = 1
ASSUME Root \in Nodes

\* ----------------------------------------------------------------------
\* Bounded successor relation (overridden for Succ by the .cfg)
\* Each node has exactly two successors, giving a non‑trivial graph.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 1 -> {2, 3}
       [] n = 2 -> {3, 4}
       [] n = 3 -> {1, 4}
       [] n = 4 -> {1, 2}
  ]

\* ----------------------------------------------------------------------
\* Bounded sequence operator (replaces Seq from Sequences)
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Path definition using the bounded successor relation
\* ----------------------------------------------------------------------
Path(s) ==
  /\ Len(s) >= 1
  /\ Head(s) = Root
  /\ \A i \in 1..(Len(s)-1) : s[i+1] \in ConnectedToSomeButNotAll[s[i]]

\* ----------------------------------------------------------------------
\* Set of nodes reachable from Root via a bounded path
\* ----------------------------------------------------------------------
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Path(s)
        /\ Last(s) = n }

\* ----------------------------------------------------------------------
\* State variables of the sequential Misra reachability algorithm
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc
vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {Root}
  /\ Frontier = {Root}
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\* One algorithmic step: pick a node from Frontier, mark it, add
\* its unmarked successors to Frontier
\* ----------------------------------------------------------------------
Step ==
  /\ pc = "Run"
  /\ \E n \in Frontier :
        /\ Marked'   = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ Marked')
        /\ pc'       = IF Frontier' = {} THEN "Done" ELSE "Run"

\* ----------------------------------------------------------------------
\* Stuttering step when the algorithm has terminated
\* ----------------------------------------------------------------------
Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<Marked, Frontier, pc>>

Next == Step \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 == \A n \in Marked :
         ConnectedToSomeButNotAll[n] \subseteq Marked \cup Frontier

Inv2 == Marked \subseteq Reachable

Inv3 == Reachable \subseteq Marked \cup Frontier

PartialCorrectness ==
  (pc = "Done") => (Marked = Reachable)

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====