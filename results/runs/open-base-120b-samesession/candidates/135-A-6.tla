---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Operator that will replace Succ in the configuration
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll == 
  [n \in Nodes |-> 
    CASE n = "n1" -> {"n2","n3"},
         n = "n2" -> {"n3","n4"},
         n = "n3" -> {"n1","n4"},
         n = "n4" -> {"n1","n2"},
         OTHER    -> {}]

\*--------------------------------------------------------------------
\* Bounded version of Seq for model checking
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables (inherited from the sequential algorithm)
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Helper definition: set of all nodes reachable from Root via
\* a bounded sequence of successors
\*--------------------------------------------------------------------
Reachable == 
  { n \in Nodes : 
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

\*--------------------------------------------------------------------
\* Initial state (inherited)
\*--------------------------------------------------------------------
Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

\*--------------------------------------------------------------------
\* Transition relation (inherited)
\*--------------------------------------------------------------------
Next == 
  \/ /\ pc = "init"
        /\ pc' = "step"
        /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "step"
        /\ 
        \* mark the current frontier
        LET newMarked == marked \cup frontier IN
          /\ marked' = newMarked
          \* compute new frontier
          LET newFrontier == ( \bigcup n \in newMarked : Succ[n] ) \ setminus newMarked IN
            /\ frontier' = newFrontier
            /\ IF newFrontier = {} THEN pc' = "done" ELSE pc' = "step"
  \/ /\ pc = "done"
        /\ UNCHANGED <<marked, frontier, pc>>

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
  /\ pc \in {"init", "step", "done"}

\*--------------------------------------------------------------------
\* Algorithm invariants
\*--------------------------------------------------------------------
Inv1 == \A n \in marked : Succ[n] \subseteq marked

Inv2 == frontier = ( \bigcup n \in marked : Succ[n] ) \ setminus marked

Inv3 == marked \cup frontier = Reachable

PartialCorrectness == 
  /\ pc = "done"
  /\ marked = Reachable

\*--------------------------------------------------------------------
\* Liveness property: termination
\*--------------------------------------------------------------------
Termination == <> (pc = "done")

====