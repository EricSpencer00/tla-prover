---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* Concrete graph with 4 nodes, each having exactly two successors
ASSUME /\ Nodes = {n1, n2, n3, n4}
       /\ Root \in Nodes

\* Operator that will replace the generic Succ in the base algorithm
ConnectedToSomeButNotAll(n) ==
  CASE n = n1 -> {n2, n3}
  []  n = n2 -> {n3, n4}
  []  n = n3 -> {n1, n4}
  []  n = n4 -> {n1, n2}
  []  OTHER  -> {}

\* Finite version of Seq for model checking
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

\* Initial state (inherited from the sequential algorithm)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* One step of the sequential reachability algorithm
Next ==
  \/ /\ pc = "start"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ marked)
          /\ pc' = "start"
  \/ /\ pc = "start"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

\* Full specification
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Type correctness invariant
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

\* Invariant 1: successor closure
Inv1 == \A n \in marked : ConnectedToSomeButNotAll(n) \subseteq marked \/ frontier

\* Invariant 2: frontier consists exactly of unmarked successors of marked nodes
Inv2 ==
  frontier = { n \in Nodes :
                \E m \in marked :
                  n \in ConnectedToSomeButNotAll(m) /\ n \notin marked }

\* Reachable set defined via bounded paths
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 :
             s[i+1] \in ConnectedToSomeButNotAll(s[i]) }

\* Invariant 3: all marked nodes are reachable
Inv3 == marked \subseteq Reachable

\* Partial correctness: when done, marked equals the reachable set
PartialCorrectness == (pc = "done") => (marked = Reachable)

\* Liveness property: the algorithm eventually terminates
Termination == <> (pc = "done")

====