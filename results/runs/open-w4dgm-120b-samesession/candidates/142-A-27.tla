---- MODULE ReachableProofs ----
EXTENDS ReachableRSM, ReachableLemmas

CONSTANTS Nodes, Root

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in { "idle", "running", "done" }

Inductive ==
    /\ TypeOK
    /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == ReachableFrom(Nodes, marked) \cup ReachableFrom(Nodes, frontier) = ReachableFrom(Nodes, marked \cup frontier)
Invariant3 == ReachableFrom(Nodes, Root) = marked \cup ReachableFrom(Nodes, frontier)
Termination == pc = "done" => ReachableFrom(Nodes, Root) = marked
====