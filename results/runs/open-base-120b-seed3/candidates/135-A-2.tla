---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Concrete successor relation: each node has exactly two successors
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    LET a == (n % Cardinality(Nodes)) + 1
        b == ((n + 1) % Cardinality(Nodes)) + 1
    IN {a, b}]

\*--------------------------------------------------------------------
\* Bounded sequence operator used to make the model finite
\*--------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Initial state (inherits the algorithm's initialisation)
\*--------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\*--------------------------------------------------------------------
\* Next-state relation (inherits the algorithm's step)
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "start"
     /\ frontier # {}
     /\ LET n == CHOOSE x \in frontier : TRUE
        IN /\ marked'   = marked \cup {n}
           /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked)
           /\ pc'       = "start"
  \/ /\ pc = "start"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

vars == <<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Reachable set defined via bounded sequences
\*--------------------------------------------------------------------
ReachableSet ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ Last(s) = n
        /\ \A i \in 1..(Len(s)-1) :
            s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  }

\*--------------------------------------------------------------------
\* Invariants required by the .cfg file
\*--------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

Inv1 ==
  \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked

Inv2 ==
  frontier \subseteq Nodes \ marked

Inv3 ==
  marked = ReachableSet

PartialCorrectness ==
  (pc = "done") => (marked = ReachableSet)

\*--------------------------------------------------------------------
\* Liveness property (termination)
\*--------------------------------------------------------------------
Termination == <> (pc = "done")

====