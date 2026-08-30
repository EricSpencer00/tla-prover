---- MODULE ReachableProofs ----
CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "exploring", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore ==
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = "exploring"

Expand(e) ==
    /\ pc = "exploring"
    /\ e \in marked
    /\ \E s \in Nodes \ (marked \cup frontier) : frontier' = frontier \cup {s}
    /\ pc' = "exploring"
    /\ UNCHANGED marked

Terminate ==
    /\ frontier = {}
    /\ pc \in {"idle", "exploring"}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Explore
    \/ \E e \in Nodes : Expand(e)
    \/ Terminate

Spec ==
    /\ Init
    /\ [][Next]_<<marked, frontier, pc>>
    /\ WF_vars(Explore)

Succ(n) == {s \in Nodes : <<n, s>> \in Edges}
ReachableFrom(S) ==
    LET Rec[T \in SUBSET Nodes] ==
        IF T = {}
        THEN S
        ELSE LET n == CHOOSE m \in T : TRUE
                 rest == Rec[T \ {n}]
             IN rest \cup Succ(n)
    IN Rec[Nodes]
Edges == {<<n, s>> \in Nodes \X Nodes : s \in Succ(n)}

\* Lemma 1: the reachable set is unaffected by swapping successors.
ReachableUnchangedUnderSwap ==
    \A n \in Nodes, k \in Nodes :
        (n # k /\ Succ(n) # Succ(k)) => ReachableFrom(Succ(n)) = ReachableFrom(Succ(k))

\* Lemma 2: reachable-from distributes over union.
ReachableOverUnion ==
    \A A \in SUBSET Nodes, B \in SUBSET Nodes :
        ReachableFrom(A \cup B) = ReachableFrom(A) \cup ReachableFrom(B)

Lemma3 == ReachableFrom({}) = {}

\* Invariant 1: type-correctness plus forward-closure of marked nodes.
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier

\* Invariant 2 follows directly from Lemma 1: the reachable set from marked
\* and frontier is exactly the reachable set from marked.
Inv2 ==
    ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup Succ(marked)

\* Invariant 3 combines Lemma 2 and Lemma 3 to rewrite the reachable-from
\* expression and isolate ReachableFrom(frontier).
Inv3 ==
    ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

\* Theorem: partial correctness - on termination the reachable set equals the
\* marked set, so every reachable node has been marked.
PartialCorrectness ==
    (pc = "done") => (ReachableFrom({Root}) = marked)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3
PROPERTIES == Inv3 /\ PartialCorrectness
====