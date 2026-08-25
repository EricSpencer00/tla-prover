---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* Concrete values for the constants (can be overridden by a .cfg file)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root \in Nodes

\* Operator that will replace Succ in the configuration
ConnectedToSomeButNotAll(n) ==
  IF n = 1 THEN {2, 3}
  ELSE IF n = 2 THEN {3, 4}
  ELSE IF n = 3 THEN {4, 1}
  ELSE IF n = 4 THEN {1, 2}
  ELSE {}

\* Bounded version of the sequence type
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

\* Initial state
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

\* One step of the sequential reachability algorithm
Next ==
  \/ /\ pc = "init"
     /\ pc' = "step"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "step"
     /\ LET newMarked == marked \cup frontier,
            newFrontier == (UNION { Succ[n] : n \in frontier }) \ newMarked
        IN
           /\ marked' = newMarked
           /\ frontier' = newFrontier
           /\ IF newFrontier = {} THEN pc' = "done" ELSE pc' = "step"
           /\ UNCHANGED <<>>
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc>>

\* Specification
Spec ==
  Init /\ [][Next]_<<marked, frontier, pc>>

\* Type correctness invariant
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

\* Helper: a node is reachable from Root via a bounded path
Reachable(n) ==
  \E s \in LimitedSeq :
    /\ Len(s) > 0
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]

\* Invariant 1: successors of marked nodes stay within marked ∪ frontier
Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Invariant 2: frontier equals the set of reachable but not yet marked nodes
Inv2 ==
  frontier = { n \in Nodes : Reachable(n) /\ n \notin marked }

\* Invariant 3: marked equals the set of all reachable nodes
Inv3 ==
  marked = { n \in Nodes : Reachable(n) }

\* Partial correctness: when finished, marked contains exactly the reachable nodes
PartialCorrectness ==
  pc = "done" => marked = { n \in Nodes : Reachable(n) }

\* Liveness property: the algorithm eventually terminates
Termination ==
  <> (pc = "done")
====