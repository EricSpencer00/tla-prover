---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\*  Finite version of Sequences: sequences of elements from a set S whose
\*  length is bounded by the number of nodes (so the model checker sees a
\*  finite domain).
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\*  Succ is overridden in the .cfg by the operator ConnectedToSomeButNotAll.
\*  We simply forward to the constant Succ.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\*  State variables of the sequential reachability algorithm.
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\*  Initial state: only the root is in the frontier, nothing is marked,
\*  and the program counter is set to "start".
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "start"

\* ----------------------------------------------------------------------
\*  One step of the algorithm.
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "start"
       /\ pc' = "running"
       /\ UNCHANGED <<Marked, Frontier>>
    \/ /\ pc = "running"
       /\ Frontier # {}
       /\ \E n \in Frontier :
            /\ Marked' = Marked \cup {n}
            /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked)
            /\ pc' = "running"
    \/ /\ pc = "running"
       /\ Frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<Marked, Frontier>>

\* ----------------------------------------------------------------------
\*  Specification of the algorithm.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\*  Type correctness invariant.
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"start", "running", "done"}

\* ----------------------------------------------------------------------
\*  Invariant 1: Successor closure – every successor of a marked node is
\*  either already marked or waiting in the frontier.
\* ----------------------------------------------------------------------
Inv1 ==
    \A n \in Marked :
        ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

\* ----------------------------------------------------------------------
\*  Invariant 2: Reachability decomposition – the root is always either
\*  marked or in the frontier.
\* ----------------------------------------------------------------------
Inv2 ==
    Root \in Marked \/ Frontier

\* ----------------------------------------------------------------------
\*  Invariant 3: Reachable set equality – every node that is marked or in the
\*  frontier is reachable from the root via a bounded path.
\* ----------------------------------------------------------------------
ReachableFromRoot(n) ==
    \E p \in LimitedSeq(Nodes) :
        /\ Len(p) > 0
        /\ Head(p) = Root
        /\ Last(p) = n
        /\ \A i \in 1..(Len(p)-1) :
              p[i+1] \in ConnectedToSomeButNotAll(p[i])

Inv3 ==
    \A n \in (Marked \cup Frontier) : ReachableFromRoot(n)

\* ----------------------------------------------------------------------
\*  Partial correctness – when the algorithm terminates, the set Marked
\*  equals exactly the set of nodes reachable from the root.
\* ----------------------------------------------------------------------
PartialCorrectness ==
    /\ pc = "done"
    /\ Marked = { n \in Nodes : ReachableFromRoot(n) }

\* ----------------------------------------------------------------------
\*  Liveness property: the algorithm eventually reaches the completed state.
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")
====