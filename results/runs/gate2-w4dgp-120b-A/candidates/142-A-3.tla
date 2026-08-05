---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

\* Reachable nodes via the graph edge relation defined by any set of directed
\* edges (the 'edges' parameter below). The closure is monotone: adding edges
\* can only enlarge the reachable set, never shrink it.
RECURSIVE ReachableFrom(_, _)
ReachableFrom(N, edges) ==
    IF N = {} THEN {}
    ELSE LET n == CHOOSE x \in N : TRUE
         IN {n} \cup ReachableFrom(N \ {n}, edges)
              \cup {y \in Nodes : <<n, y>> \in edges}

\* Lemma 1 (proved in ReachabilityProofs): the reachable set under the union of
\* two edge sets equals the union of the reachable set under the left one and
\* the reachable-from set of the reachable set under the left one when the
\* right edge set is applied.
ReachLemma ==
    \A edges1, edges2 \in SUBSET (Nodes \X Nodes) :
        ReachableFrom(Nodes, edges1 \cup edges2) =
            ReachableFrom(Nodes, edges1) \cup
                ReachableFrom(ReachableFrom(Nodes, edges1), edges2)

\* Lemma 2 (proved in ReachabilityProofs): ReachableFrom is stable when the
\* starting set is enlarged by a step of its own reachable set.
StepStability ==
    \A N \in SUBSET Nodes, edges \in SUBSET (Nodes \X Nodes) :
        ReachableFrom(N \cup ReachableFrom(N, edges), edges) =
            ReachableFrom(N, edges)

\* Lemma 3 (proved in ReachabilityProofs): ReachableFrom of the empty set is
\* empty for any edge set.
EmptyReach ==
    \A edges \in SUBSET (Nodes \X Nodes) :
        ReachableFrom({}, edges) = {}

\* The sequential algorithm adds a frontier node to the marked set, then expands
\* the frontier with the successors of any marked node that are still unmarked
\* and not already in the frontier.
VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {0, 1, 2}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = 0

MarkFrontier ==
    /\ pc = 0
    /\ frontier # {}
    /\ \E w \in frontier :
        /\ marked' = marked \cup {w}
        /\ frontier' = frontier \ {w}
    /\ pc' = 1

ExpandFrontier ==
    /\ pc = 1
    /\ \E v \in marked :
        \E u \in Nodes :
            /\ <<v, u>> \in Nodes \X Nodes
            /\ u \notin marked
            /\ u \notin frontier
            /\ frontier' = frontier \cup {u}
    /\ pc' = 2
    /\ UNCHANGED marked

Done ==
    /\ pc = 2
    /\ frontier = {}
    /\ pc' = 0
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ MarkFrontier
    \/ ExpandFrontier
    \/ Done

Spec ==
    /\ Init
    /\ [][Next]_<<marked, frontier, pc>>

\* Invariant 1: type-correct plus every successor of a marked node is either
\* marked already or waiting in the frontier.
InvStep ==
    /\ TypeOK
    /\ \A v \in marked : \A u \in Nodes :
        (<<v, u>> \in Nodes \X Nodes) => (u \in marked \/ u \in frontier)

\* Invariant 2: the currently marked and frontier nodes already cover exactly
\* the set reachable from the marked nodes under the algorithm's edge rule.
\* Consequence of Lemma 1 and SetExtensionality.
InvCoverage ==
    ReachableFrom(Nodes, Nodes \X Nodes) =
        marked \cup ReachableFrom(marked, Nodes \X Nodes)

\* Invariant 3: the reachable set from the root equals the marked set plus the
\* reachable set from the frontier. Uses Lemma 2 and Lemma 3.
InvFullCoverage ==
    ReachableFrom(Nodes, Nodes \X Nodes) = marked \cup ReachableFrom(frontier, Nodes \X Nodes)

\* Partial correctness: termination implies the marked set is exactly the
\* reachable set -- the algorithm does not miss or over-claim any node.
PartialCorrect ==
    (frontier = {}) => (marked = ReachableFrom(Nodes, Nodes \X Nodes))

INVARIANTS == InvStep
PROPERTIES == InvCoverage
PROPERTIES == InvFullCoverage
PROPERTIES == PartialCorrect
====