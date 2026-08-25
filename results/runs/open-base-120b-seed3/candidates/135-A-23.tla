---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\*=============================================================================
\* Configuration-specific operator substituting for Succ
\*=============================================================================
ConnectedToSomeButNotAll(n) == Succ[n]

\*=============================================================================
\* Finite version of Seq for model checking
\*=============================================================================
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*=============================================================================
\* State variables (inherited from the sequential reachability algorithm)
\*=============================================================================
VARIABLES Marked, Frontier, pc

\*=============================================================================
\* Derived sets
\*=============================================================================
Reachable ==
  { n \in Nodes :
      \E p \in LimitedSeq(Nodes) :
        /\ Len(p) > 0
        /\ p[1] = Root
        /\ p[Len(p)] = n
        /\ \A i \in 1..Len(p)-1 :
            p[i+1] \in ConnectedToSomeButNotAll(p[i])
  }

\*=============================================================================
\* Type correctness invariant
\*=============================================================================
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

\*=============================================================================
\* Initialization (inherited)
\*=============================================================================
Init ==
  /\ Marked = {Root}
  /\ Frontier = ConnectedToSomeButNotAll(Root) \ Marked
  /\ pc = "init"

\*=============================================================================
\* Next-state relation (inherited)
\*=============================================================================
Next ==
  \/ /\ pc = "init"
     /\ pc' = "step"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "step"
     /\ \E n \in Frontier :
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked')
          /\ pc' = IF Frontier' = {} THEN "done" ELSE "step"
          /\ UNCHANGED pc
  \/ /\ pc = "done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

\*=============================================================================
\* Specification
\*=============================================================================
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\*=============================================================================
\* Algorithm invariants
\*=============================================================================
Inv1 == \A n \in Marked : ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier
Inv2 == Marked \cap Frontier = {}
Inv3 == \A n \in Nodes :
          (n \in Marked \/ n \in Frontier) => n \in Reachable

\*=============================================================================
\* Partial correctness property
\*=============================================================================
PartialCorrectness ==
  (Frontier = {} ) => Marked = Reachable

\*=============================================================================
\* Liveness property (termination)
\*=============================================================================
Termination == <> (Frontier = {})

\*=============================================================================
\* Exported identifiers for the .cfg file
\*=============================================================================
\* The .cfg expects the following names:
\*   SPECIFICATION  -> Spec
\*   INVARIANTS     -> TypeOK, Inv1, Inv2, Inv3, PartialCorrectness
\*   PROPERTIES     -> Termination
\*   CONSTANTS      -> Nodes, Root, Succ
\*   ALSO operator  -> ConnectedToSomeButNotAll (substituted for Succ)
\*   ALSO operator  -> LimitedSeq   (replaces Seq)
\*=============================================================================

====