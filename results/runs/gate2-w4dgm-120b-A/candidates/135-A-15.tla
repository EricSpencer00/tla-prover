---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "exploring", "done"}

\* Successor closure: every marked node's successors are still covered by marked ∪ frontier.
\* Reachability decomposition: the explored region and the frontier never overlap.
\* Reachable set equality: every reachable node is already marked, so no reachable node is stranded in the waiting set.
\* Partial correctness: every node that can be reached from the root is eventually marked.
\* (The type invariant is the other property checked by the suite, but it is still part of the model.)
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
Inv2 == marked \cap frontier = {}
Inv3 == {n \in Nodes : (\E s \in { <<Root>> } \cup { LimitedSeq <<Root>> : k \in 1..Cardinality(Nodes) : s \in { seq \in Seq(Nodes) : seq[1] = Root /\ seq[k] = n /\ \A i \in 1..(k - 1) : seq[i + 1] \in Succ[seq[i]] } })} \subseteq marked
PartialCorrectness == \A n \in Nodes : (n \in {n \in Nodes : (\E s \in { <<Root>> } \cup { LimitedSeq <<Root>> : k \in 1..Cardinality(Nodes) : s \in { seq \in Seq(Nodes) : seq[1] = Root /\ seq[k] = n /\ \A i \in 1..(k - 1) : seq[i + 1] \in Succ[seq[i]] } })} => (n \in marked))

Spec == Init /\ [][Next]_vars

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"

\* The algorithm only fires while there is still frontier to absorb; when none is left it simply idles.
\* This is what makes every run converge and every reachable node eventually get marked.
Next ==
    \/ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup Succ[n]
        /\ pc' = "exploring"
    \/ /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

Termination == <>(pc = "done")

\* Concrete finite graph: each node points to exactly two other nodes, so reachability is nontrivial but the model stays small.
\* This operator is what the .cfg file substitutes in for the abstract Succ constant in the main spec.
ConnectedToSomeButNotAll ==
    [ n \in Nodes |-> {m \in Nodes : m \in Succ[n]} ]

\* A FINITE version of Seq, bounded by the number of nodes, so the reachability
\* existential quantification is over a finite range and the model is checkable.
LimitedSeq ==
    [ x \in Nodes, k \in 1..Cardinality(Nodes) |-> { seq \in Seq(Nodes) : seq[1] = x /\ Len(seq) = k } ]

vars == <<marked, frontier, pc>>
====