---- MODULE Reachable ----
EXTENDS FiniteSets, Sequences, Naturals, TLC

CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Edge == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

Reach(S) == 
  S \cup { n \in Nodes : \E s \in S : <<s, n>> \in TC(Edge) }

\*--------------------------------------------------------------------
\* Operator required by the .cfg substitution
\* (Succ will be replaced by ConnectedToSomeButNotAll)
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\*--------------------------------------------------------------------
\* Finite version of Seq required by the .cfg substitution
\*--------------------------------------------------------------------
LimitedSeq(S) == {}

\*--------------------------------------------------------------------
\* Initialization
\*--------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"
  /\ Root \in Nodes
  /\ Succ \in [Nodes -> SUBSET Nodes]

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
  \/ /\ frontier # {}
     /\ \E n \in frontier:
          \/ /\ n \notin marked
              /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
              /\ pc' = pc
          \/ /\ n \in marked
              /\ marked' = marked
              /\ frontier' = frontier \ {n}
              /\ pc' = pc
  \/ /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

\*--------------------------------------------------------------------
\* Invariants required by the .cfg file
\*--------------------------------------------------------------------
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == (frontier = {}) => marked = Reach({Root})

\*--------------------------------------------------------------------
\* Liveness property (termination)
\*--------------------------------------------------------------------
Termination == <> (pc = "done")

\*--------------------------------------------------------------------
\* The set of all invariants for checking
\*--------------------------------------------------------------------
\* (the .cfg file will refer to these by name)
\*--------------------------------------------------------------------
\* End of module
=============================================================================