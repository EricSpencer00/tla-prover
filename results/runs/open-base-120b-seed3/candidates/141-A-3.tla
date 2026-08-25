---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Operator substituted by the .cfg file (overriding Succ).  It is defined
\* here for completeness; the model checker will replace Succ with this
\* operator.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* A finite version of the sequence operator Seq (replaces Seq in the
\* configuration).  Here we simply alias it; the .cfg will supply a
\* bounded definition if needed.
\* ----------------------------------------------------------------------
LimitedSeq == Seq(Nodes)

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Reachability operator: all nodes reachable from a set S via zero or
\* more Succ steps.
\* ----------------------------------------------------------------------
REACH(S) ==
  { n \in Nodes :
      \E path \in Seq(Nodes) :
        /\ Len(path) >= 1
        /\ path[1] \in S
        /\ path[Len(path)] = n
        /\ \A i \in 1..Len(path)-1 : path[i+1] \in Succ[path[i]]
  }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"
  /\ TypeOK

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Main transition relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ frontier = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ frontier # {}
     /\ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ pc' = "Running"
          /\ UNCHANGED <<>>
  \/ /\ frontier # {}
     /\ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ pc' = "Running"
          /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
  REACH(marked \cup frontier) = marked \cup REACH(frontier)

Inv3 ==
  REACH({Root}) = marked \cup REACH(frontier)

PartialCorrectness ==
  (frontier = {} => marked = REACH({Root}))

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (frontier = {} /\ pc = "Done")

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES == Termination

=============================================================================