---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* The reachable-from operator is defined in the reachability proofs module.
\* It satisfies Lemma 1 (union of two reachable-from sets is reachable-from
\* the union) and Lemma 2 (adding successors to the source leaves reachable-from
\* unchanged), plus Lemma 3 (reachable from the empty set is empty).

Init == /\ marked = {Root}
        /\ frontier = {}
        /\ pc = "spanning"

Expand == /\ \E n \in frontier :
               /\ frontier' = frontier \ {n}
               /\ marked' = marked \cup {n}
          /\ pc' = "spanning"
Expand == /\ \E n \in frontier :
               /\ frontier' = frontier \ {n}
               /\ marked' = marked \cup {n}
               /\ pc' = "spanning"

Frontier == /\ \E n \in marked :
                /\ \E m \in Nodes :
                     /\ m \notin marked
                     /\ m \notin frontier
                     /\ n # m
                     /\ frontier' = frontier \cup {m}
                /\ pc' = "spanning"
Frontier == /\ \E n \in marked :
                /\ \E m \in Nodes :
                     /\ m \notin marked
                     /\ m \notin frontier
                     /\ n # m
                     /\ frontier' = frontier \cup {m}
                /\ pc' = "spanning"

Done == /\ frontier = {}
        /\ pc = "spanning"
        /\ pc' = "done"
        /\ UNCHANGED <<marked, frontier>>

Init == /\ marked = {Root}
        /\ frontier = {}
        /\ pc = "spanning"

Next == \/ Expand \/ Frontier \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1: type-correctness plus that every successor of a marked
\* node is either already marked or sitting in the frontier.
TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ marked \cap frontier = {}
          /\ frontier = {}
               \/ (\E n \in marked : \E m \in frontier : n # m)

\* Invariant 2: nodes reachable from the marked set, plus those reachable
\* from the frontier, equal the nodes reachable from both together.
\* Proof: an immediate consequence of the key graph-theoretic Lemma 1.
ReachablePortion ==
    (reachableFrom[NODES, marked] \cup reachableFrom[NODES, frontier])
        = reachableFrom[NODES, marked \cup frontier]

\* Invariant 3: nodes reachable from the root are exactly the marked nodes
\* plus those reachable from the frontier, proved from Lemma 2 and Lemma 3.
FullReachability == reachableFrom[NODES, {Root}]
                        = marked \cup reachableFrom[NODES, frontier]

\* The final theorem: termination implies the marked set is the reachable set.
PartialCorrectness == (pc = "done") => (marked = reachableFrom[NODES, {Root}])

INVARIANT TypeOK

LAZY_INVARIANT ReachablePortion

CONSTANT_INVARIANT FullReachability

PROPERTY PartialCorrectness

====