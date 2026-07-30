---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* The frontier and the marked set may overlap, which is the core relaxation
\* that lets Misra's algorithm be parallelized.
Explore ==
  /\ frontier # {}
  /\ pc = "start"
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = "start"

Terminate ==
  /\ frontier = {}
  /\ pc = "start"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Explore)
        /\ WF_vars(Terminate)

\* Every successor of a marked node already lies in the marked set or in the
\* frontier (the reachable region is saturated outside the frontier).
Inv1 ==
  \A n \in marked : \A s \in Succ[n] : s \in marked \cup frontier

\* The region reachable from the union of marked and frontier equals the
\* region reachable from the marked set plus whatever the frontier can reach.
Inv2 ==
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

\* The reachable region from the root splits exactly into the marked set and
\* whatever the frontier can still reach.
Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom({Root}))

Termination ==
  (FinteNodes(Nodes)) ~> (pc = "done")

\* Reachable-from is the usual closure: start from S and follow successors.
ReachableFrom(S) ==
  LET F[T \in SUBSET Nodes] ==
       IF T = {} THEN {}
       ELSE LET x == CHOOSE y \in T : TRUE
            IN Succ[x] \cup F[T \ {x}]
  IN F[S]

\* The model's termination proof only needs a finite node set; the algorithm
\* itself works for infinite graphs too.
FinteNodes(X) == X # {} /\ \A Y \in SUBSET X : \E k \in Nat : \A y \in Y : y \in 1..k

\* .cfg substitution: the reachable-from operator is swapped for a bounded
\* connected-to operator in the model. Define it here with that name.
ConnectedToSomeButNotAll(n) == Succ[n]

\* .cfg substitution for the bounded version of Seq. It is reachable only as
\* Seq when the operator on the right of \E is substituted in.
LimitedSeq ==
  LET S[T \in SUBSET Nodes] ==
       IF T = {} THEN <<>>
       ELSE LET x == CHOOSE y \in T : TRUE
            IN <<x>> \circ S[T \ {x}]
  IN S[Nodes]

====