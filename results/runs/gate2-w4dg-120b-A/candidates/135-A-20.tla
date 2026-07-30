---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS
    Nodes,
    Root,
    Succ,
    Seq

\* Marked: nodes reached by the algorithm. Frontier: the current wavefront
\* of nodes with unexplored successors. pc: the program counter (0 = running,
\* 1 = done). The algorithm itself is the classic sequential Misra breadth-
\* first saturation; this module only fixes the graph and caps sequences.
VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {0, 1}

\* Reachability is defined via the existence of a path between two nodes,
\* which needs a bounded sequence type for exhaustive checking.
Reachable(x, y) ==
    \E s \in Seq : /\ Len(s) >= 2
                       /\ s[1] = x
                       /\ s[Len(s)] = y
                       /\ \A i \in 1 .. Len(s) - 1 : s[i + 1] \in Succ[s[i]]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = 0

Step ==
    /\ frontier # {}
    /\ pc = 0
    /\ \E x \in frontier :
         /\ \E y \in Succ[x] :
              /\ y \notin marked
              /\ marked' = marked \cup {y}
              /\ frontier' = (frontier \cup {y}) \ {x}
    /\ UNCHANGED pc

Done ==
    /\ pc = 0
    /\ frontier = {}
    /\ pc' = 1
    /\ UNCHANGED << marked, frontier >>

Next == Step \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1: the frontier always stays inside the discovered set.
Inv1 == frontier \subseteq marked

\* Invariant 2: discovered nodes are closed under taking successors.
Inv2 == \A x \in marked : \A y \in Succ[x] : y \in marked

\* Invariant 3: the discovered set is exactly the reachable set from the root.
Inv3 == marked = { y \in Nodes : Reachable(Root, y) }

PartialCorrectness == Root \in marked

Termination == pc = 1

====