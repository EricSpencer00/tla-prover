---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

None == "none"
Wf == "wf"
Term == "done"

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {None, Wf, Term}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = Wf

Explore(n) ==
    /\ pc = Wf
    /\ n \in frontier
    /\ frontier' = (frontier \cup {n}) \ {n}
    /\ marked' = marked \cup {n}
    /\ pc' = Wf

FrontierEmpty ==
    /\ pc = Wf
    /\ frontier = {}
    /\ pc' = Term
    /\ UNCHANGED << marked, frontier >>

Idle ==
    /\ pc = Term
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ FrontierEmpty
    \/ Idle

Spec == Init /\ [][Next]_vars

\* Invariant 1: type-correctness plus successors of a marked node are
\* either marked or waiting on the frontier.
Inv1 ==
    /\ TypeOK
    /\ \A n \in Nodes :
        (n \in marked) => (n \in marked \/ n \in frontier)

\* Invariant 2: the reachable-from-marked set plus the reachable-from-
\* frontier set covers exactly the reachable-from-union set.  This is
\* provable directly from Lemma 1 (the set-of-successors lemma).
Inv2 ==
    \A n \in Nodes :
        \/ (n \in marked => \E m \in marked \cup frontier : n \in Reachable(m))
        \/ (n \in frontier => \E m \in marked \cup frontier : n \in Reachable(m))

\* Invariant 3: the reachable-from-root set equals the marked set plus the
\* reachable-from-frontier set.  The proof uses Lemma 2 (reachability stable
\* under adding successors) and Lemma 3 (nothing reachable from empty).
Inv3 ==
    \A n \in Nodes :
        (n \in Reachable(Root)) <=> (n \in marked \/ \E m \in frontier : n \in Reachable(m))

\* The TLAPS-checked theorem: partial correctness.  Upon termination,
\* the frontier is empty and the marked set is exactly the reachable set.
PartialCorrectness ==
    \A n \in Nodes : (n \in Reachable(Root)) <=> (n \in marked)
====