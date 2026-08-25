---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* Constants that will be instantiated in the .cfg file
\*--------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Operator that provides a finite successor set for each node.
\* The .cfg substitutes this operator for the generic Succ operator.
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\*--------------------------------------------------------------------
\* Bounded version of Seq, used to keep the state space finite.
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables of the sequential reachability algorithm
\*--------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

\*--------------------------------------------------------------------
\* Helper definition of the set of nodes reachable from Root via
\* paths of bounded length.
\*--------------------------------------------------------------------
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1 .. Len(s)-1 : s[i+1] \in ConnectedToSomeButNotAll(s[i])
  }

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"step", "done"}

\*--------------------------------------------------------------------
\* Invariant 1: successor closure (all successors of nodes already
\* discovered are either marked or waiting in the frontier)
\*--------------------------------------------------------------------
Inv1 ==
  \A n \in Marked :
    ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

\*--------------------------------------------------------------------
\* Invariant 2: every marked node is reachable from the root
\*--------------------------------------------------------------------
Inv2 == Marked \subseteq Reachable

\*--------------------------------------------------------------------
\* Invariant 3: every reachable node is either already marked or
\* still pending in the frontier
\*--------------------------------------------------------------------
Inv3 == Reachable \subseteq Marked \cup Frontier

\*--------------------------------------------------------------------
\* Partial correctness: when the algorithm terminates, the set of
\* marked nodes equals the set of all reachable nodes.
\*--------------------------------------------------------------------
PartialCorrectness == (pc = "done") => (Marked = Reachable)

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ pc = "step"
  /\ Marked = {Root}
  /\ Frontier = {Root}
  /\ TypeOK

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "step"
     /\ Frontier # {}
     /\ \E n \in Frontier :
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked)
          /\ pc' = "step"
          /\ TypeOK
  \/ /\ pc = "step"
     /\ Frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>
     /\ TypeOK

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Invariants to be checked
\*--------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

\*--------------------------------------------------------------------
\* Liveness property: the algorithm eventually terminates
\*--------------------------------------------------------------------
Termination == <> (pc = "done")

====