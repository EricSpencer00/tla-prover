---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* Concrete assumptions for the model checking instance
ASSUME /\ Nodes = {1, 2, 3, 4}
ASSUME /\ Root \in Nodes
ASSUME /\ Cardinality(Nodes) = 4

\* Bounded version of Seq for path quantification
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\* Concrete successor relation (overridden for Succ via the .cfg)
ConnectedToSomeButNotAll == 
  [n \in Nodes |-> 
    CASE n = 1 -> {2, 3}
    [] n = 2 -> {3, 4}
    [] n = 3 -> {1, 4}
    [] n = 4 -> {1, 2}
  ]

\* State variables inherited from the sequential reachability algorithm
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* Initial state
Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "Step"

\* One exploration step
Step ==
  /\ pc = "Step"
  /\ \E n \in frontier :
       LET succs == ConnectedToSomeButNotAll[n] IN
         /\ marked'   = marked \cup succs
         /\ frontier' = (frontier \ {n}) \cup (succs \ marked)
         /\ pc'       = "Step"

\* Termination action
Done ==
  /\ pc = "Step"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Done

\* Full specification
Spec == Init /\ [][Next]_vars

\* Type correctness invariant
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Step", "Done"}

\* Successor‑closure invariant
Inv1 ==
  \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked

\* Frontier is always a subset of the marked set
Inv2 == frontier \subseteq marked

\* Definition of reachable nodes via bounded paths
Path(n) ==
  \E s \in LimitedSeq :
       /\ Len(s) >= 1
       /\ s[1] = Root
       /\ s[Len(s)] = n
       /\ \A i \in 1 .. Len(s)-1 :
            s[i+1] \in ConnectedToSomeButNotAll[s[i]]

Reachable == { n \in Nodes : Path(n) }

\* Equality of the marked set with the set of reachable nodes
Inv3 == marked = Reachable

\* Partial correctness: when algorithm terminates, it has discovered exactly the reachable nodes
PartialCorrectness ==
  (frontier = {} /\ pc = "Done") => marked = Reachable

\* Liveness property: the algorithm eventually terminates
Termination == <> (frontier = {} /\ pc = "Done")
=================================================