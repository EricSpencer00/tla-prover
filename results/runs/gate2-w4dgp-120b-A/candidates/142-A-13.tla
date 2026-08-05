---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachableDefs
\* The Reachable module provides the adjacency function succ, the Reachable
\* set type, the ReachableFrom set-of-nodes operator, and the graph lemmas.
CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init == /\ marked = {}
        /\ frontier = {Root}
        /\ pc = 0
\* A frontier node is explored: its successors are marked or put into the
\* frontier, and it is removed from the frontier.
Explore == /\ pc = 0
           /\ frontier # {}
           /\ \E n \in frontier :
                /\ marked' = marked \cup {n}
                /\ frontier' = (frontier \ {n}) \cup (succ[n] \ marked)
                /\ pc' = pc
           /\ UNCHANGED pc
\* Everything reachable is marked, and the frontier is exhausted: the
\* algorithm has finished its work.
Done == /\ frontier = {}
        /\ \A n \in Nodes : (n \in Reachable) => n \in marked
        /\ pc' = 1
        /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Done

Spec == Init /\ [][Next]_vars
\* Inductive invariant: type-correct, and every successor of a marked node
\* is already marked or sitting in the frontier.
TypeOK == /\ marked \in SUBSET Nodes
          /\ frontier \in SUBSET Nodes
          /\ pc \in 0..1
          /\ \A n \in marked : succ[n] \subseteq marked \cup frontier
\* Reachable nodes are precisely those reachable from the known frontier.
FrontierCover == Reachable = ReachableFrom(frontier \cup marked)
\* Reachable set equals marked plus those reachable from the frontier.
FrontierComplete == Reachable = marked \cup ReachableFrom(frontier)
\* Termination: marked nodes are exactly the reachable nodes.
Termination == frontier = {} => marked = Reachable

INVARIANTS TypeOK, FrontierCover, FrontierComplete
PROPERTIES Termination
====