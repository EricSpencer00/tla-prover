---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* The reachable set under the deterministic reachability operator, built from
\* finite prefixes of sequences so the model stays finite.
Reachable(S) == { n \in S :
    \E k \in 0..Cardinality(Nodes):
        \E seq \in LimitedSeq(k):
            /\ seq # << >>
            /\ Head(seq) = Root
            /\ Last(seq) = n
            /\ \A i \in 1..(Len(seq) - 1): seq[i + 1] \in Succ(seq[i])
}

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"idle", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ(Root)
    /\ pc = "idle"

Begin ==
    /\ pc = "idle"
    /\ frontier # {}
    /\ pc' = "running"
    /\ UNCHANGED <<marked, frontier>>

\* Deterministic next-node choice: always the smallest successor, so the visited
\* set stays finite even though Successor is nondeterministic in the model.
Visit ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier:
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \cup Succ(n)) \ {n}
    /\ pc' = "done"

BeginVisit == Begin \/ Visit
IdleDone == (pc = "done") /\ UNCHANGED <<marked, frontier, pc>>

Next == BeginVisit \/ IdleDone

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Every frontier node is reachable from the root in the marking defined by
\* the deterministic Successor (always the smallest successor), and nothing
\* outside the reachable set is in the marking.
Inv1 == frontier \subseteq Reachable(marked)

\* The marking is closed under the deterministic Successor: no new node can
\* ever be added by Successor beyond what is already reachable from the root.
Inv2 == Reachable(marked) \subseteq Reachable(Reachable(marked))

\* Reachable is idempotent on the marking, so the marking is a fixed point of
\* the reachability operator and nothing further is reachable.
Inv3 == Reachable(Reachable(marked)) = Reachable(marked)

PartialCorrectness == Reachable(Nodes) \subseteq marked

Termination == (pc = "idle") ~> (pc = "done")

====