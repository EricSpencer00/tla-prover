---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES visited, frontier, pc
vars == <<visited, frontier, pc>>

TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}
    /\ Root \in Nodes
    /\ Succ \in [Nodes -> SUBSET Nodes]
    /\ Seq \in Nat

Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "run"

BFSStep ==
    /\ pc = "run"
    /\ frontier # {}
    /\ \E x \in frontier :
         /\ frontier' = frontier \ {x}
         /\ IF x \in visited
              THEN frontier' = frontier' \cup {}
              ELSE /\ visited' = visited \cup {x}
                   /\ frontier' = frontier' \cup Succ[x]
    /\ pc' = IF frontier' = {} THEN "done" ELSE "run"

Next == BFSStep

Spec == Init /\ [][Next]_vars
            /\ WF_vars(BFSStep)

Inv1 ==
    /\ \A n \in visited : Succ[n] \subseteq visited \cup frontier
    /\ \A v \in frontier : Succ[v] \subseteq visited \cup frontier

Inv2 ==
    \A M \in SUBSET Nodes :
        (\A n \in M : Succ[n] \subseteq M) =>
            (visited \cup frontier) \subseteq M =>
                (VisitedFrom(frontier) \cup visited) \subseteq M

Inv3 == VisitedFrom({Root}) = visited \cup VisitedFrom(frontier)

PartialCorrectness == pc = "done" => visited = VisitedFrom({Root})

Termination == pc = "done"

VisitedFrom(S) ==
    LET f[T \in SUBSET Nodes] ==
        IF T = {} THEN {}
        ELSE
            LET x == CHOOSE y \in T : TRUE
            IN Succ[x] \cup f[T \ {x}]
    IN f[S]

====