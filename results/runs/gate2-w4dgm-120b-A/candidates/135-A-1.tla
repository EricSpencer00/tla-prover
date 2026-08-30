---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes, Root, Succ

\* The state variables (marked, frontier, pc) come from the base
\* reachability algorithm; this module only supplies the concrete
\* graph structure (Succ) and the bounded sequence override.
VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

\* The marking step: nondeterministically pick any frontier node and
\* mark it along with all of its immediate successors, then remove it
\* from the frontier. This is the only action that grows the reachable
\* set, so the reachable region can only ever advance outward.
MarkStep(n) ==
    /\ n \in frontier
    /\ marked' = marked \cup {n} \cup Succ[n]
    /\ frontier' = frontier \ {n}
    /\ pc' = "running"

Prepare ==
    /\ pc = "idle"
    /\ frontier # {}
    /\ pc' = "running"
    /\ UNCHANGED <<marked, frontier>>

\* The algorithm is finished once the frontier is empty (nothing left to
\* explore) or the reachable set already covers the whole graph.
Terminate ==
    /\ pc = "running"
    /\ \/ frontier = {}
       \/ marked = Nodes
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

ExplorationStep == \E n \in Nodes : MarkStep(n)

Next == ExplorationStep \/ Prepare \/ Terminate

Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(ExplorationStep) /\ WF_vars(Prepare) /\ WF_vars(Terminate)

Inv1 == frontier \subseteq Nodes \ marked

Inv2 == marked = {m \in Nodes : \E p \in Seq(Nodes) : p # <<>> /\ Head(p) = m /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]}

Inv3 == \A n \in Nodes : (n \in marked) => (n \in Succ[Root] \/ \E m \in Nodes : (n \in Succ[m] /\ m \in marked))

PartialCorrectness == \A n \in Nodes : (n \in marked) ~> (n \in marked)

Termination == <>(pc = "done")

\* Each node has exactly two successors, chosen deterministically so
\* the graph is finite and fully specified without leaving any node
\* with an empty successor set (which would make the reachable set
\* trivial and uninteresting from a coverage-testing perspective).
ConnectedToSomeButNotAll ==
    /\ Succ[Root] = {Root, IF Root = 1 THEN 2 ELSE 1}
    /\ Succ[IF Root = 1 THEN 2 ELSE 1] = {Root, 2}
    /\ Succ[2] = {Root, IF Root = 1 THEN 2 ELSE 1}
    /\ Cardinality(Nodes) = 3

\* The reachable set can never exceed the graph (by construction it
\* never pulls in a node out of thin air) and can never shrink below
\* the frontier (the frontier is always a subset of marked).
ReachableSetBounds == /\ frontier \subseteq marked
                       /\ marked \subseteq Nodes

\* Overrides the infinite sequence type from Sequences with a
\* bounded one so the model is finite and checkable; the bound is
\* exactly the number of nodes, which is sufficient to cover the
\* longest possible simple path in this graph.
LimitedSeq == {s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes)}

====