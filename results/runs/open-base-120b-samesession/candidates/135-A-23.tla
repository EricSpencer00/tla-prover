---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Concrete graph definition (4 nodes, each with exactly 2 successors)
\*--------------------------------------------------------------------
NodeSet == {1, 2, 3, 4}
\* The model must assign Nodes = NodeSet and Root = 1 in the .cfg file,
\* but we provide a default definition for documentation purposes.
\* (These definitions are ignored if the constants are bound externally.)
NodesDef == NodeSet
RootDef  == 1

\* Edge set describing the deterministic 2‑successor graph
Graph == {
    <<1, 2>>, <<1, 3>>,
    <<2, 3>>, <<2, 4>>,
    <<3, 1>>, <<3, 4>>,
    <<4, 1>>, <<4, 2>>
}

\*--------------------------------------------------------------------
\* Operator that provides a finite successor function.
\* The .cfg file substitutes Succ with ConnectedToSomeButNotAll,
\* so the algorithm uses this operator as its successor relation.
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
    { m \in Nodes : <<n, m>> \in Graph }

\*--------------------------------------------------------------------
\* Bounded version of the sequence type used in reachability definitions.
\* The .cfg file substitutes Seq with LimitedSeq.
\*--------------------------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables of the sequential reachability algorithm
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "step"

\*--------------------------------------------------------------------
\* One step of the algorithm
\*--------------------------------------------------------------------
Next ==
    \/ /\ pc = "step"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
            /\ pc' = IF (frontier' = {}) THEN "done" ELSE "step"
    \/ /\ pc = "step"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"step", "done"}

\*--------------------------------------------------------------------
\* Invariant 1: successor closure
\*--------------------------------------------------------------------
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\*--------------------------------------------------------------------
\* Invariant 2: marked and frontier are disjoint
\*--------------------------------------------------------------------
Inv2 ==
    marked \cap frontier = {}

\*--------------------------------------------------------------------
\* Helper: set of nodes reachable from Root via a bounded path
\*--------------------------------------------------------------------
ReachableFromRoot ==
    { n \in Nodes :
        \E s \in LimitedSeq(Nodes) :
            /\ Len(s) >= 1
            /\ Len(s) <= Cardinality(Nodes)
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
    }

\*--------------------------------------------------------------------
\* Invariant 3: the marked set equals the set of reachable nodes
\*--------------------------------------------------------------------
Inv3 ==
    marked = ReachableFromRoot

\*--------------------------------------------------------------------
\* Partial correctness: when finished, all reachable nodes are marked
\*--------------------------------------------------------------------
PartialCorrectness ==
    (pc = "done") => (marked = ReachableFromRoot)

\*--------------------------------------------------------------------
\* Liveness property: the algorithm eventually terminates
\*--------------------------------------------------------------------
Termination ==
    <> (pc = "done")

\*--------------------------------------------------------------------
\* The set of invariants and properties used by the .cfg file
\*--------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES == Termination

=============================================================================