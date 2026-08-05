---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"init", "searching", "done"}

\* Successor closure of the marked set is always contained in the marked set itself.
Inv1 == \A n \in Nodes : n \in marked => Succ[n] \subseteq marked

\* Every node outside the marked set has a predecessor inside it.
Inv2 == \A n \in Nodes : n \notin marked => \E m \in marked : n \in Succ[m]

\* The marked set equals the nodes reachable from the root via any sequence of successors.
Inv3 ==
    /\ marked = {n \in Nodes : \E s \in LimitedSeq(Nodes) : Len(s) >= 1 /\ s[1] = Root /\ s[Len(s)] = n /\ \A k \in 1..(Len(s) - 1) : s[k + 1] \in Succ[s[k]]}
    /\ Root \in marked

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "init"

Search ==
    /\ pc = "init"
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \cup Succ[n]) \ {n}
    /\ pc' = "searching"

MarkComplete ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == Search \/ MarkComplete \/ Done

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

PartialCorrectness == pc = "done" => frontier = {}

Termination == <>(pc = "done")

====