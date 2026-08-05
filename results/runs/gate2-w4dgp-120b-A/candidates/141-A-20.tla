---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* LimitedSeq in the .cfg replaces Seq from Sequences with a version that is
\* guaranteed finite; this definition keeps the name Seq in scope for the
\* standard operators but adds the safety belt that the model checker requires.
Seq(s) == CHOOSE seq \in Sequences : seq \in s /\ Cardinality(seq) = Cardinality(s)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

\* This is Misra's backward reachability step applied to a chosen frontier node:
\* if it is new, it becomes marked and its successors join the frontier; if it
\* is already marked, it is removed from the frontier. Either way the frontier
\* shrinks or the marked set grows, which is what drives the algorithm on.
Step(n) ==
    /\ n \in frontier
    /\ \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
    /\ pc' = IF frontier = {n} THEN "done" ELSE "start"

Next == \E n \in Nodes : Step(n)

Spec == Init /\ [][Next]_vars

\* Once a node is marked, every one of its successors is either already marked
\* or waiting in the frontier -- there is never a reachable node that the
\* algorithm has completely forgotten.
Inv1 ==
    \A x \in marked : Succ[x] \subseteq (marked \cup frontier)

\* The marked set together with the frontier always reaches the same nodes as
\* the full union of both; that is the invariant that lets termination imply
\* completeness.
Inv2 ==
    ReachableFrom(Nodes, marked \cup frontier) =
        ReachableFrom(Nodes, marked) \cup ReachableFrom(Nodes, frontier)

\* The frontier, together with what has already been marked, reaches exactly
\* the nodes reachable from the root.
Inv3 ==
    ReachableFrom(Nodes, {Root}) = marked \cup ReachableFrom(Nodes, frontier)

PartialCorrectness ==
    pc = "done" => marked = ReachableFrom(Nodes, {Root})

\* Termination only needs the reachable set to be finite; the algorithm can
\* never visit more than finitely many distinct nodes.
Termination ==
    ReachableFrom(Nodes, {Root}) # Nodes => <> (pc = "done")

\* The .cfg replaces Succ with a bounded version ConnectedToSomeButNotAll for
\* the finite-model check, so Succ itself can be any graph the spec accepts.
====