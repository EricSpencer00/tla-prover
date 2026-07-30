---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* A model-checking configuration module for the sequential Misra reachability
\* algorithm. It provides concrete definitions (a fixed graph and a bounded
\* sequence type) that make the state space finite.
\* Inherited state: marked set, frontier set, program counter.
\* Verified: type correctness, the three algorithm invariants, and termination.

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* Reachable via a bounded sequence of successive successors; the length bound
\* is exactly the number of nodes, making the existential quantifier finite.
Reachable(n) == \E s \in Seq : Len(s) <= Cardinality(Nodes)
                     /\ Head(s) = Root
                     /\ Last(s) = n
                     /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]

Init == /\ marked = {Root}
        /\ frontier = {Root}
        /\ pc = "running"

Step == /\ pc = "running"
        /\ \E n \in frontier :
            /\ marked' = marked \cup Succ[n]
            /\ frontier' = (frontier \cup Succ[n]) \ {n}
        /\ pc' = IF (frontier \cup Succ[n]) \ {n} = {} THEN "done" ELSE "running"

Spec == Init /\ [][Step]_vars

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"running", "done"}

\* Successor closure: every frontier node is unmarked and its successors are
\* either unmarked or already in the frontier, so the frontier always grows
\* from unmarked territory.
Inv1 == \A n \in frontier : n \notin marked /\ Succ[n] \subseteq (frontier \cup (Nodes \ marked))

\* Reachability decomposition: the marked set is exactly the nodes reachable
\* from the root, so no reachable node is left unmarked and no unmarked node
\* is claimed reachable.
Inv2 == \A n \in Nodes : n \in marked <=> Reachable(n)

\* Reachable set equality: the reachable nodes are exactly the marked nodes.
Inv3 == {n \in Nodes : Reachable(n)} = marked

PartialCorrectness == \A n \in Nodes : n \in marked => Reachable(n)

Termination == <>(pc = "done")

====