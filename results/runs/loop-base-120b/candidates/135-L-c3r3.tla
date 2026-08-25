---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root

\* Concrete graph definition (4 nodes, each with exactly 2 successors)
ASSUME Nodes = {"A", "B", "C", "D"}
ASSUME Root \in Nodes

\* ----------------------------------------------------------------------
\* Operator that will replace the abstract Succ in the algorithm
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CASE n = "A" -> {"B", "C"}
  []  n = "B" -> {"C", "D"}
  []  n = "C" -> {"D", "A"}
  []  n = "D" -> {"A", "B"}
  []  OTHER     -> {}

\* Provide the original name expected by the algorithm; it will be
\* overridden by the .cfg substitution with ConnectedToSomeButNotAll.
Succ(n) == ConnectedToSomeButNotAll(n)

\* ----------------------------------------------------------------------
\* Finite version of the generic Seq operator (bounded by |Nodes|)
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Initial state (algorithm's Init)
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "run"

\* ----------------------------------------------------------------------
\* Helper: one step of the reachability exploration
\* ----------------------------------------------------------------------
ProcessStep ==
  /\ Frontier /= {}
  /\ LET n == CHOOSE x \in Frontier : TRUE
     IN /\ Marked'   = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup ConnectedToSomeButNotAll(n)
        /\ pc'       = "run"

\* ----------------------------------------------------------------------
\* Helper: termination when no frontier remains
\* ----------------------------------------------------------------------
Done ==
  /\ Frontier = {}
  /\ Marked' = Marked
  /\ Frontier' = Frontier
  /\ pc' = "done"

\* ----------------------------------------------------------------------
\* Next-state relation (inherited from the algorithm)
\* ----------------------------------------------------------------------
Next == ProcessStep \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Reachable set defined via bounded sequences
\* ----------------------------------------------------------------------
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ Head(s) = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..(Len(s)-1) :
            s[i+1] \in ConnectedToSomeButNotAll(s[i])
  }

\* ----------------------------------------------------------------------
\* Invariant 1: successor closure
\* ----------------------------------------------------------------------
Inv1 ==
  \A n \in Marked :
    ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: every marked node is reachable
\* ----------------------------------------------------------------------
Inv2 ==
  Marked \subseteq Reachable

\* ----------------------------------------------------------------------
\* Invariant 3: frontier is a subset of reachable nodes
\* ----------------------------------------------------------------------
Inv3 ==
  Frontier \subseteq Reachable

\* ----------------------------------------------------------------------
\* Partial correctness: when done, all reachable nodes are marked
\* ----------------------------------------------------------------------
PartialCorrectness ==
  (pc = "done") => (Marked = Reachable)

\* ----------------------------------------------------------------------
\* Liveness property: the algorithm eventually terminates
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")
====