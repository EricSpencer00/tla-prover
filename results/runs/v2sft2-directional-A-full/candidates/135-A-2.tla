---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
NodesSet == Nodes

\* Succ is a function from each node to a finite set of successor nodes
\* (at most 2 successors, deterministic graph)
SuccFunc == [ n \in NodesSet |-> { m \in NodesSet : m \in Succ[n] } ]

\* Seq is a function mapping each node to a finite sequence of nodes
SeqFunc == [ n \in NodesSet |-> { s \in Seq[n] } ]

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Initial state (inherited from the algorithm, instantiated with the graph)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = { Root }
    /\ pc = "Scan"

\* ----------------------------------------------------------------------
\* Actions (inherited from the algorithm, unchanged)
\* ----------------------------------------------------------------------
Scan ==
    /\ pc = "Scan"
    /\ \E n \in frontier :
          \E s \in SeqFunc[n] :
              /\ s[#1] \in frontier
              /\ s \subset marked
              /\ \A i \in 1..Len(s)-1 :
                    s[i] \in SuccFunc[s[#i]]
              /\ marked' = marked \cup { s[Len(s)] }
              /\ frontier' = frontier \ { s[Len(s)] }
              /\ pc' = "Scan"
    \/ \E n \in frontier :
          /\ marked' = marked
          /\ frontier' = frontier
          /\ pc' = "Done"

Next == Scan

Spec == Init /\ [] [Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked : SUBSET NodesSet
    /\ frontier : SUBSET NodesSet
    /\ pc \in {"Scan", "Done"}

\* ----------------------------------------------------------------------
\* Algorithm invariants
\* ----------------------------------------------------------------------
Inv1 == marked \subseteq NodesSet

Inv2 ==
    \A n \in marked :
        \E m \in SuccFunc[n] :
            m \in marked

Inv3 ==
    marked = { n \in NodesSet : n \in SuccFunc* [Root] }

\* ----------------------------------------------------------------------
\* Partial correctness property (the reachable set eventually equals the
\* closure of the root under the successor relation).
\* ----------------------------------------------------------------------
PartialCorrectness == Inv3

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination ==
    []<> (pc = "Done")

====