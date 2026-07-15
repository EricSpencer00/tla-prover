---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\* -------------------------------------------------
CONSTANTS
    Nodes,   \* The finite set of node identifiers
    Root,    \* The distinguished start node
    Succ,    \* A function mapping each node to a non‑empty set of its successors
    Seq      \* An abstract sequence type (override for TLC)

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES
    marked,   \* Nodes that have been discovered
    frontier, \* Nodes pending exploration
    pc        \* Program counter, representing which step of the algorithm we are in

\* -------------------------------------------------
\* Type definitions (helpful for readability and TypeOK)
\* -------------------------------------------------
Node == Nodes

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ marked   = {Root}
    /\ frontier = {Root}
    /\ pc       = "Run"

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
UnvisitedSuccessors(s) ==
    \E v \in s : \E w \in Succ[v] : w \notin marked

\* -------------------------------------------------
\* Actions
\* -------------------------------------------------
Run ==
    \/ /\ pc = "Run"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
            /\ pc'       = "Run"
    \/ /\ pc = "Run"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>

\* -------------------------------------------------
\* Stuttering step to allow the model checker to advance after termination
\* -------------------------------------------------
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next == Run \/ Stutter

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* -------------------------------------------------
\* Safety invariants
\* -------------------------------------------------
\* Type correctness
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

\* Inv1: Successor closure – every node in marked has its successors either already in marked or awaiting in frontier
Inv1 ==
    \A n \in marked :
        \A s \in Succ[n] :
            s \in marked \/ s \in frontier

\* Inv2: Reachability decomposition – all nodes in frontier are reachable from Root via a path whose intermediate nodes are already marked
Inv2 ==
    \A n \in frontier :
        \E p \in Seq :
            /\ Len(p) >= 1
            /\ p[1] = Root
            /\ p[Len(p)] = n
            /\ \A i \in 1..Len(p)-1 :
                   p[i] \in marked
            /\ \A i \in 1..Len(p)-1 :
                   p[i+1] \in Succ[p[i]]

\* Inv3: Equality of reachable set – when the algorithm is done, marked equals the set of all nodes reachable from Root
Inv3 ==
    /\ pc = "Done"
    /\ marked = { n \in Nodes :
                    \E p \in Seq :
                        /\ Len(p) >= 1
                        /\ p[1] = Root
                        /\ p[Len(p)] = n
                        /\ \A i \in 1..Len(p)-1 :
                               p[i+1] \in Succ[p[i]] }

\* Partial correctness – the algorithm finishes with exactly the reachable nodes marked
PartialCorrectness ==
    Inv3

\* -------------------------------------------------
\* Liveness property: eventual termination
\* -------------------------------------------------
Termination == <> (pc = "Done")

====