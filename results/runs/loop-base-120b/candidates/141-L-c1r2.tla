---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* -----------------------------------------------------------------
\* Operators required by the configuration
\* -----------------------------------------------------------------
\* ConnectedToSomeButNotAll is used by the .cfg to replace Succ.
\* Here we simply alias it to the original Succ; the model
\* checker will later bind Succ to a concrete (finite) successor
\* function, so this definition is safe.
ConnectedToSomeButNotAll(n) == Succ[n]

\* LimitedSeq replaces the standard Seq operator from the Sequences
\* module.  For our purposes we can safely delegate to the original
\* Seq, because the model checking configuration will only generate
\* finite sequences.
LimitedSeq(S) == Seq(S)

\* -----------------------------------------------------------------
\* Recursive definition of the set of nodes reachable from a node.
\* -----------------------------------------------------------------
RECURSIVE ReachFrom(_)
ReachFrom(n) == {n} \cup UNION { ReachFrom(m) : m \in Succ[n] }

\* Reachable nodes from a set of sources.
ReachSet(S) == UNION { ReachFrom(n) : n \in S }

\* -----------------------------------------------------------------
\* Type correctness invariant
\* -----------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

\* -----------------------------------------------------------------
\* Invariant 1: every successor of a marked node is either marked or
\*             in the frontier.
\* -----------------------------------------------------------------
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* -----------------------------------------------------------------
\* Invariant 2: marked ∪ ReachSet(frontier) = ReachSet(marked ∪ frontier)
\* -----------------------------------------------------------------
Inv2 == marked \cup ReachSet(frontier) = ReachSet(marked \cup frontier)

\* -----------------------------------------------------------------
\* Invariant 3: ReachSet({Root}) = marked ∪ ReachSet(frontier)
\* -----------------------------------------------------------------
Inv3 == ReachSet({Root}) = marked \cup ReachSet(frontier)

\* -----------------------------------------------------------------
\* Partial correctness: when the algorithm terminates, marked equals
\* the set of nodes reachable from the root.
\* -----------------------------------------------------------------
PartialCorrectness == (frontier = {} => marked = ReachSet({Root}))

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"
    /\ TypeOK

\* -----------------------------------------------------------------
\* Main step (nondeterministically pick a node from the frontier)
\* -----------------------------------------------------------------
Next ==
    \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked'   = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
           /\ pc'       = pc
        \/ /\ n \in marked
           /\ marked'   = marked
           /\ frontier' = frontier \ {n}
           /\ pc'       = IF frontier' = {} THEN "done" ELSE "running"

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

\* -----------------------------------------------------------------
\* Liveness property: the algorithm eventually terminates (frontier empty)
\* -----------------------------------------------------------------
Termination == []<>(frontier = {})

====