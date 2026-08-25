---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Operator that will replace the generic Succ operator in the algorithm
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\*--------------------------------------------------------------------
\* A finite version of the sequence type, bounded by the number of nodes
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables of the sequential reachability algorithm
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Helper definition: the set of nodes reachable from a given node via
\* a bounded path (using LimitedSeq)
\*--------------------------------------------------------------------
ReachableFrom(r) ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ Head(s) = r
        /\ Last(s) = n
        /\ \A i \in 1 .. (Len(s) - 1) :
             s[i+1] \in ConnectedToSomeButNotAll[s[i]] }

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Init"

\*--------------------------------------------------------------------
\* Step action: process one node from the frontier
\*--------------------------------------------------------------------
Step ==
  /\ (pc = "Init") \/ (pc = "Running")
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked')
       /\ pc' = "Running"

\*--------------------------------------------------------------------
\* Termination action: no more frontier nodes
\*--------------------------------------------------------------------
Done ==
  /\ frontier = {}
  /\ pc = "Running"
  /\ pc' = "Done"
  /\ UNCHANGED << marked, frontier >>

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next == Step \/ Done

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
  /\ pc \in {"Init", "Running", "Done"}

\*--------------------------------------------------------------------
\* Invariant 1: successor closure (all successors of marked nodes are
\* either already marked or waiting in the frontier)
\*--------------------------------------------------------------------
Inv1 ==
  \A n \in marked :
    ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

\*--------------------------------------------------------------------
\* Invariant 2: frontier and marked are disjoint
\*--------------------------------------------------------------------
Inv2 ==
  marked \cap frontier = {}

\*--------------------------------------------------------------------
\* Invariant 3: the union of marked and frontier equals the set of
\* nodes reachable from the root (within the bounded sequence length)
\*--------------------------------------------------------------------
Inv3 ==
  marked \cup frontier = ReachableFrom(Root)

\*--------------------------------------------------------------------
\* Partial correctness: when the algorithm terminates, all reachable
\* nodes are marked
\*--------------------------------------------------------------------
PartialCorrectness ==
  pc = "Done" => marked = ReachableFrom(Root)

\*--------------------------------------------------------------------
\* Liveness property: the algorithm eventually reaches the Done state
\*--------------------------------------------------------------------
Termination == <> (pc = "Done")
====