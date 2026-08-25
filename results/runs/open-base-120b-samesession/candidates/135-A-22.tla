---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Concrete graph definition (each node has exactly two successors)
\* The configuration substitutes Succ with ConnectedToSomeButNotAll,
\* so we provide that operator here.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2,3}
  []  n = 2 -> {1,4}
  []  n = 3 -> {1,4}
  []  n = 4 -> {2,3}
  []  OTHER -> {}

\* ----------------------------------------------------------------------
\* Bounded version of the generic sequence operator
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables of the sequential Misra reachability algorithm
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "Init"

\* ----------------------------------------------------------------------
\* One step of the algorithm
\* ----------------------------------------------------------------------
Step ==
  \/ /\ Frontier # {}
     /\ \E n \in Frontier :
          /\ Marked'   = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked)
          /\ pc'       = "Active"
          /\ UNCHANGED <<>>
  \/ /\ Frontier = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<Marked, Frontier>>

\* ----------------------------------------------------------------------
\* Overall specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Step]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"Init", "Active", "Done"}

\* ----------------------------------------------------------------------
\* Invariant 1: successor closure
\* ----------------------------------------------------------------------
Inv1 ==
  \A n \in Marked :
      ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: reachability decomposition (Root is either marked,
\*   in the frontier, or the algorithm has finished)
\* ----------------------------------------------------------------------
Inv2 ==
  (Root \in Marked) \/ (Root \in Frontier) \/ (pc = "Done")

\* ----------------------------------------------------------------------
\* Helper definition: set of nodes reachable from Root via a bounded path
\* ----------------------------------------------------------------------
Reachable ==
  { n \in Nodes :
      \E p \in LimitedSeq(Nodes) :
        /\ Len(p) > 0
        /\ p[1] = Root
        /\ \A i \in 1..(Len(p)-1) : p[i+1] \in ConnectedToSomeButNotAll(p[i])
        /\ p[Len(p)] = n }

\* ----------------------------------------------------------------------
\* Invariant 3: marked set equals the set of reachable nodes
\* ----------------------------------------------------------------------
Inv3 ==
  Marked = Reachable

\* ----------------------------------------------------------------------
\* Partial correctness: upon termination the algorithm has computed the
\* exact reachable set
\* ----------------------------------------------------------------------
PartialCorrectness ==
  (pc = "Done") => (Marked = Reachable)

\* ----------------------------------------------------------------------
\* Liveness property: the algorithm eventually reaches the completed state
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====