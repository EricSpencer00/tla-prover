---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* The finite path definition overrides the unbounded one from Sequences for
\* model checking.  It is deliberately a subtype of Seq, never a redefinition.
LimitedSeq(S) == { x \in Seq(S) : Len(x) <= Cardinality(Nodes) }

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "searching", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "searching"

\* No modification: the actions come straight from the sequential algorithm.
Next ==
    \/ \E w \in Nodes : /\ pc = "searching" /\ w \in frontier /\ marked' = marked \cup {w} /\ frontier' = frontier \cup (Succ[w] \ {w}) /\ pc' = "searching"
    \/ pc = "searching" /\ frontier = {} /\ pc' = "done" /\ UNCHANGED <<marked, frontier>>
    \/ pc = "done" /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv1 == \A x \in frontier : \E y \in marked : \E s \in LimitedSeq(Nodes) : s[1] = y /\ s[Len(s)] = x /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]
Inv2 == marked \subseteq { y \in Nodes : \E x \in Nodes : x \in frontier \cup {Root} /\ \E s \in LimitedSeq(Nodes) : s[1] = Root /\ s[Len(s)] = y /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]] }
Inv3 == frontier \subseteq { y \in Nodes : \E x \in Nodes : x \in marked /\ \E s \in LimitedSeq(Nodes) : s[1] = x /\ s[Len(s)] = y /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]] }
PartialCorrectness == (pc = "done") => (marked = { y \in Nodes : \E s \in LimitedSeq(Nodes) : s[1] = Root /\ s[Len(s)] = y /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]] })
Termination == (pc # "done") ~> (pc = "done")
====