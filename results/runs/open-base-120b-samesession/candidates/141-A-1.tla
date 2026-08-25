---- MODULE Reachable ----
EXTENDS Sequences, Naturals, TLC

CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
LimitedSeq(S) == Seq(S)   \* finite sequences over S

\* Successor function used in the algorithm (may be overridden by cfg)
ConnectedToSomeButNotAll(n) == Succ[n]

\* Reachability from a set of nodes using finite paths
Reach(S) ==
  UNION {
    n \in Nodes :
      \E path \in LimitedSeq(Nodes) :
        /\ Len(path) >= 1
        /\ path[1] \in S
        /\ \A i \in 1 .. Len(path)-1 : path[i+1] \in Succ[path[i]]
        /\ n = path[Len(path)]
  }

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
PickNode ==
  \E n \in frontier :
    /\ pc = "Run"
    /\ IF n \notin marked THEN
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \cup Succ[n]
         /\ UNCHANGED pc
       ELSE
         /\ marked' = marked
         /\ frontier' = frontier \ {n}
         /\ UNCHANGED pc

Terminate ==
  /\ pc = "Run"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next == PickNode \/ Terminate

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
  (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
  Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
  /\ pc = "Done"
  /\ marked = Reach({Root})
  /\ frontier = {}

\*--------------------------------------------------------------------
\* Liveness property
\*--------------------------------------------------------------------
Termination == <> (pc = "Done")

\*--------------------------------------------------------------------
\* Theorem declarations (required by the .cfg file)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====