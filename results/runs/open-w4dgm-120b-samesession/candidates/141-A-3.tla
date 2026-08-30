---- MODULE Reachable ----
\* Misra's variant of BFS for graph reachability: the visited set and the frontier
\* may overlap, which simplifies parallelization. The module defines every
\* identifier the reference TLC configuration expects.
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc

TypeOK == /\ visited \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"running", "done"}

RECURSIVE ReachableFrom(_, _)
ReachableFrom(V, S) ==
    IF S = {} THEN V
    ELSE LET n == CHOOSE x \in S : TRUE
         IN ReachableFrom(V \cup Succ[n], S \ {n})

RECURSIVE ReachableFromSet(_)
ReachableFromSet(S) ==
    IF S = {} THEN {}
    ELSE LET n == CHOOSE x \in S : TRUE
         IN Succ[n] \cup ReachableFromSet(S \ {n})

Init == /\ visited = {}
        /\ frontier = {Root}
        /\ pc = "running"

\* The main action has two cases, chosen nondeterministically from the frontier.
Explore(f) == /\ pc = "running"
              /\ f \in frontier
              /\ visited' = IF f \in visited
                            THEN visited
                            ELSE visited \cup {f}
              /\ frontier' = IF f \in visited
                             THEN frontier \ {f}
                             ELSE frontier \cup Succ[f]
              /\ pc' = IF frontier \ {f} = {}
                       THEN IF f \in visited THEN "done" ELSE pc
                       ELSE pc

Terminate == /\ pc = "running"
             /\ frontier = {}
             /\ pc' = "done"
             /\ UNCHANGED <<visited, frontier>>

Next == (\E f \in Nodes: Explore(f)) \/ Terminate

Spec == Init /\ [][Next]_<<visited, frontier, pc>>

\* Every successor of a visited node is either already visited or waiting in the
\* frontier; visited nodes are exactly those reachable from the root.
Inv1 == \A n \in visited : Succ[n] \subseteq (visited \cup frontier)
Inv2 == (visited \cup frontier) \cup ReachableFromSet(frontier) =
        ReachableFromSet(visited \cup frontier)
Inv3 == ReachableFromSet({Root}) = visited \cup ReachableFromSet(frontier)
PartialCorrectness == pc = "done" => visited = ReachableFromSet({Root})

Termination == (frontier # {}) ~> (frontier = {})

\* The .cfg expects these as operators; the name on the left is replaced by the
\* name on the right, so define the right-hand side only -- keep the extension.
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====