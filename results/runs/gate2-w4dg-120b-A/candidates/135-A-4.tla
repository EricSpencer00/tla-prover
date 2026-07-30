---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

\* The misreachability module is instantiated over a concrete graph and a
\* bounded sequence space so that TLC can explore a finite state space.
\* Each node has exactly 2 successors, chosen to keep the reachable set
\* non-trivial but finite.
\* Succ is a function mapping each node to a non-empty set of its successors,
\* so the Reachable relation below is the reachability closure an existential
\* over a bounded sequence of successors, not an unbounded one.

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "search", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "init"

StepMark ==
    /\ pc = "init"
    /\ pc' = "search"
    /\ UNCHANGED <<marked, frontier>>

StepExplored ==
    /\ pc = "search"
    /\ \E y \in frontier :
         /\ marked' = marked \cup {y}
         /\ frontier' = (frontier \cup Succ[y]) \ {y}
    /\ UNCHANGED pc

StepDone ==
    /\ pc = "search"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == StepMark \/ StepExplored \/ StepDone

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Reachable: there exists a sequence of successors from a marked node to x.
Reachable(x) ==
    \E y \in marked :
        \E k \in 1..Cardinality(Nodes) :
            \E s \in Seq[Nodes, k] :
                /\ s[1] = y
                /\ s[k] = x
                /\ \A i \in 1..(k - 1) : s[i + 1] \in Succ[s[i]]

\* Every frontier node is reachable from some marked node.
Inv1 ==
    \A x \in frontier : Reachable(x)

\* Every marked node is either the root or reachable from the root.
Inv2 ==
    \A x \in marked : (x = Root) \/ Reachable(x)

Inv3 ==
    \A x \in Nodes : x \in marked => Reachable(x)

PartialCorrectness ==
    \A x \in Nodes : (x \in reachable \Xor x \in marked) \/ (x \in reachable /\ x \in marked)

Termination ==
    <>(pc = "done")

====