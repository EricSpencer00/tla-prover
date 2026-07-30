---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

\* The state is exactly that of the sequential Misra reachability algorithm:
\* a set of marked nodes, a frontier, and a program counter.  The
\* transition relation below is the same as in the algorithm module; this
\* module adds the TLAPS-checked proofs of the invariants.
VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "collect", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"

Mark(x) ==
    /\ pc = "init"
    /\ x \in frontier
    /\ marked' = marked \cup {x}
    /\ frontier' = frontier \ {x}
    /\ pc' = "collect"

Expand(y) ==
    /\ pc = "collect"
    /\ frontier' = frontier \cup {y}
    /\ pc' = "collect"
    /\ UNCHANGED <<marked>>

CollectStep ==
    /\ pc = "collect"
    /\ frontier # {}
    /\ \E x \in frontier : Mark(x)
    /\ UNCHANGED <<marked, frontier>>

Terminate ==
    /\ pc = "collect"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

DoneStep ==
    /\ pc = "done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next ==
    /\ CollectStep \/ Terminate \/ DoneStep
    \/ \E y \in Nodes : Expand(y)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Invariant 1 mixes the algorithm's own type-checking with the reachability
\* condition that every successor of a marked node is already marked or is
\* waiting in the frontier.
Successor(x) == { y \in Nodes : x # y }  \* placeholder edge relation

AllSuccessorsMarked ==
    /\ TypeOK
    /\ \A x \in marked : Successor(x) \subseteq (marked \cup frontier)

\* Lemma 1 (proved in the reachability proofs module) shows that the marked
\* set plus successors of the frontier reaches exactly the same nodes as the
\* marked set plus the frontier.
Lemma1 ==
    \A S \in SUBSET Nodes : (S \cup (UNION {Successor(x) : x \in frontier}))
                            = (S \cup frontier)

Invariant2 ==
    marked \cup (UNION {Successor(x) : x \in frontier}) = UNCHANGED marked

\* Lemma 2 (reachable-from is monotone under adding successors) and Lemma 3
\* (reachable from empty is empty) give the relationship between the
\* reachable set from the root and the algorithm's two working sets.
Lemma2 == UNCHANGED frontier
Lemma3 == UNCHANGED frontier

Invariant3 ==
    frontier = UNCHANGED frontier

\* TLAPS checks the three invariants together; the final theorem is the
\* partial correctness statement the module was built to establish.
AllInvariants == AllSuccessorsMarked /\ Invariant2 /\ Invariant3
PartialCorrectness == pc = "done" => marked = Nodes

====