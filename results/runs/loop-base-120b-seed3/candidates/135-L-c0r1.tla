---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants defining the concrete graph used for model checking
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\* Concrete values (can be overridden by a .cfg file)
Nodes == 1..4
Root  == 1
\* Succ maps each node to its (exactly two) successors.
Succ == [n \in Nodes |-> 
            CASE n = 1 -> {2,3}
               [] n = 2 -> {3,4}
               [] n = 3 -> {1,4}
               [] n = 4 -> {1,2}]

\* ----------------------------------------------------------------------
\* State variables of the sequential reachability algorithm
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Bounded sequence operator (replaces the unbounded Seq)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Operator that supplies the (finite) successor set for a node.
\* The .cfg file substitutes this for the constant Succ.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked   = {Root}
    /\ frontier = {Root}
    /\ pc       = "step"

\* ----------------------------------------------------------------------
\* One step of the algorithm
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "step"
       /\ \E n \in frontier :
            /\ LET succs == ConnectedToSomeButNotAll(n) IN
               /\ marked'   = marked \cup succs
               /\ frontier' = (frontier \ {n}) \cup (succs \ marked)
               /\ pc'       = IF frontier' = {} THEN "done" ELSE "step"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"step", "done"}

\* ----------------------------------------------------------------------
\* Invariant 1: frontier is always a subset of marked
\* ----------------------------------------------------------------------
Inv1 == frontier \subseteq marked

\* ----------------------------------------------------------------------
\* Helper: existence of a bounded path from Root to a node
\* ----------------------------------------------------------------------
PathTo(n) ==
    \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in ConnectedToSomeButNotAll(s[i])

\* ----------------------------------------------------------------------
\* Invariant 2: every marked node is reachable from Root
\* ----------------------------------------------------------------------
Inv2 == \A n \in marked : PathTo(n)

\* ----------------------------------------------------------------------
\* The set of all nodes reachable from Root (using bounded paths)
\* ----------------------------------------------------------------------
ReachableSet == { n \in Nodes : PathTo(n) }

\* ----------------------------------------------------------------------
\* Invariant 3: when the algorithm terminates, marked equals the reachable set
\* ----------------------------------------------------------------------
Inv3 == (pc = "done") => (marked = ReachableSet)

\* ----------------------------------------------------------------------
\* Partial correctness: at termination, all reachable nodes are marked
\* (this follows from Inv3 but is stated explicitly)
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "done") => (ReachableSet \subseteq marked)

\* ----------------------------------------------------------------------
\* Liveness property: the algorithm eventually reaches the completed state
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

====