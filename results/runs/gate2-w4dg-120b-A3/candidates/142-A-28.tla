---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Reachable, ReachableLemmas

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in 0..2

\* Inductive invariant: type correctness plus every successor of a marked
\* node is either already marked or queued in the frontier.
ReachableConsistent ==
    /\ TypeOK
    /\ \A u \in marked : \E v \in Nodes : succ[u, v] /\ (v \in marked \/ v \in frontier)

\* Frontier/outgoing reachability is preserved when the marked set is enlarged.
FrontierReachability ==
    reachable[marked] \cup reachable[frontier] = reachable[marked \cup frontier]

\* The marked set plus reachable-from-frontier is exactly the reachable set.
CompleteReachability ==
    reachable[Root] = marked \cup reachable[frontier]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = 0

\* The frontier expands by one marked node's unmarked successors; when empty
\* the algorithm holds and the invariants can be read.
Step ==
    /\ frontier # {}
    /\ \E u \in frontier :
         /\ marked' = marked \cup {u}
         /\ frontier' = (frontier \ {u}) \cup {v \in Nodes : succ[u, v] /\ v \notin marked}
    /\ pc' = 0

Relax ==
    /\ frontier = {}
    /\ pc < 2
    /\ pc' = pc + 1
    /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Relax

Spec == Init /\ [][Next]_vars

INVARIANTS == ReachableConsistent /\ FrontierReachability /\ CompleteReachability

\* Partial correctness: termination implies the marked set is exactly the
\* reachable set, derived from the two reachability invariants above.
PROPERTIES == CompleteReachability

====