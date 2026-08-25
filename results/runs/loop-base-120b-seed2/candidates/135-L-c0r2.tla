---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* Concrete graph with 4 nodes, each having exactly two successors.
\* The configuration file substitutes the generic Succ with ConnectedToSomeButNotAll,
\* which must be a constant (no arguments) of the same arity as Succ.
ConnectedToSomeButNotAll ==
  { <<1,2>>, <<1,3>>,
    <<2,3>>, <<2,4>>,
    <<3,1>>, <<3,4>>,
    <<4,1>>, <<4,2>> }

\* Helper operator to obtain the set of successors of a node from the
\* relation ConnectedToSomeButNotAll.
SuccOf(n) ==
  { m \in Nodes : <<n,m>> \in ConnectedToSomeButNotAll }

\* Finite version of Seq for model checking (bounded by the number of nodes).
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

\* Initial state (inherited from the sequential reachability algorithm).
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* One step of the sequential reachability algorithm.
Next ==
  \/ /\ pc = "start"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (SuccOf(n) \ marked)
          /\ pc' = "start"
  \/ /\ pc = "start"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

\* Full specification.
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Type correctness invariant.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

\* Invariant 1: successor closure.
Inv1 == \A n \in marked : SuccOf(n) \subseteq marked \/ frontier

\* Invariant 2: frontier consists exactly of unmarked successors of marked nodes.
Inv2 ==
  frontier = { n \in Nodes :
                \E m \in marked :
                  n \in SuccOf(m) /\ n \notin marked }

\* Reachable set defined via bounded paths.
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 :
             s[i+1] \in SuccOf(s[i]) }

\* Invariant 3: all marked nodes are reachable.
Inv3 == marked \subseteq Reachable

\* Partial correctness: when done, marked equals the reachable set.
PartialCorrectness == (pc = "done") => (marked = Reachable)

\* Liveness property: the algorithm eventually terminates.
Termination == <> (pc = "done")

====