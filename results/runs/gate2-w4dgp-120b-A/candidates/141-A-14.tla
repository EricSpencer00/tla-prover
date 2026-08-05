---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"exploring", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "exploring"

Explore(n) ==
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \cup Succ[n]
    /\ UNCHANGED pc

DropFromFrontier(n) ==
    /\ n \in frontier
    /\ n \in marked
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED <<marked, pc>>

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ \E n \in Nodes : DropFromFrontier(n)
    \/ /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E n \in Nodes : Explore(n))
    /\ WF_vars(\E n \in Nodes : DropFromFrontier(n))

Inv1 ==
    /\ \A n \in Nodes :
        /\ n \in marked => (frontier \cup marked) \cap Succ[n] \subseteq frontier \cup marked
        /\ n \in frontier => (frontier \cup marked) \cap Succ[n] \subseteq frontier \cup marked

Inv2 ==
    /\ (marked \cup frontier) \cup
        \bigcup_{n \in frontier \cup marked} Succ[n]
        \subseteq \bigcup_{n \in marked \cup frontier} Succ[n]

Inv3 ==
    /\ \bigcup_{n \in Nodes} Succ[n]
        \subseteq marked \cup \bigcup_{n \in frontier} Succ[n]

PartialCorrectness ==
    frontier = {}
        => \bigcup_{n \in Nodes} Succ[n] \cup {Root} \subseteq marked

Termination == frontier = {} ~> frontier = {}

====