---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* Concrete constants defining a finite graph with 4 nodes,
\* each node having exactly two successors.
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

Nodes == {"n1", "n2", "n3", "n4"}

Root  == "n1"

\* Succ is a total function from Nodes to subsets of Nodes.
Succ == [n \in Nodes |-> 
          CASE n = "n1" -> {"n2", "n3"}
               [] n = "n2" -> {"n3", "n4"}
               [] n = "n3" -> {"n4", "n1"}
               [] n = "n4" -> {"n1", "n2"}]

\* ----------------------------------------------------------------------
\* Operator substituted for Succ in the configuration.
\* It simply returns the successor set defined by Succ.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Bounded version of Seq to keep the model finite.
\* Sequences of length at most |Nodes|.
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables of the sequential reachability algorithm.
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Initial state.
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* ----------------------------------------------------------------------
\* One step of the algorithm.
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "start"
        /\ pc' = "process"
        /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "process"
        /\ \E n \in frontier :
             /\ marked'   = marked \cup {n}
             /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
             /\ pc' = IF frontier' = {} THEN "done" ELSE "process"
  \/ /\ pc = "done"
        /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant.
\* ----------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "process", "done"}

\* ----------------------------------------------------------------------
\* Helper: existence of a path from Root to n using LimitedSeq.
\* ----------------------------------------------------------------------
ReachablePath(n) ==
  \E p \in LimitedSeq(Nodes) :
    /\ Len(p) > 0
    /\ p[1] = Root
    /\ p[Len(p)] = n
    /\ \A i \in 1..Len(p)-1 : p[i+1] \in Succ[p[i]]

\* ----------------------------------------------------------------------
\* Invariant 1: successor closure.
\* ----------------------------------------------------------------------
Inv1 ==
  \A n \in marked :
    \A m \in Succ[n] : m \in marked \/ m \in frontier

\* ----------------------------------------------------------------------
\* Invariant 2: every frontier node is reachable from Root.
\* ----------------------------------------------------------------------
Inv2 ==
  \A n \in frontier : ReachablePath(n)

\* ----------------------------------------------------------------------
\* Invariant 3: marked set equals the set of all reachable nodes.
\* ----------------------------------------------------------------------
Inv3 ==
  marked = { n \in Nodes : ReachablePath(n) }

\* ----------------------------------------------------------------------
\* Partial correctness: when algorithm finishes, frontier is empty and
\* marked contains exactly the reachable nodes.
\* ----------------------------------------------------------------------
PartialCorrectness ==
  (pc = "done") => (frontier = {} /\ marked = { n \in Nodes : ReachablePath(n) })

\* ----------------------------------------------------------------------
\* Specification of the system.
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Liveness property: the algorithm eventually terminates.
\* ----------------------------------------------------------------------
Termination ==
  <> (pc = "done")

=============================================================================