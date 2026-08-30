---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

RECURSIVE ReachFrom(_, _)
ReachFrom(S, w) ==
    IF w = {} THEN {}
    ELSE LET x == CHOOSE y \in w : TRUE
             rest == ReachFrom(S, w \ {x})
         IN IF x \in S THEN S \cup rest
            ELSE (S \cup {x}) \cup rest

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}
    /\ Root \in Nodes

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Mark(x) ==
    /\ pc = "working"
    /\ x \in frontier
    /\ frontier' = frontier \ {x}
    /\ marked' = marked \cup {x}
    /\ UNCHANGED pc

Expand(x, y) ==
    /\ pc = "working"
    /\ x \in marked
    /\ y \notin marked
    /\ y \notin frontier
    /\ frontier' = frontier \cup {y}
    /\ UNCHANGED << marked, pc >>

BecomeWorking ==
    /\ pc = "idle"
    /\ frontier # {}
    /\ pc' = "working"
    /\ UNCHANGED << marked, frontier >>

BecomeDone ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Restart ==
    /\ pc = "done"
    /\ pc' = "idle"
    /\ marked' = {}
    /\ frontier' = {Root}

Next ==
    \/ \E x \in Nodes : Mark(x)
    \/ \E x \in Nodes, y \in Nodes : Expand(x, y)
    \/ BecomeWorking
    \/ BecomeDone
    \/ Restart

MarkStep == \E x \in Nodes : Mark(x)
ExpandStep == \E x \in Nodes, y \in Nodes : Expand(x, y)
WorkStep == MarkStep \/ ExpandStep
IdleStep == BecomeWorking \/ Restart

Spec == Init /\ [][Next]_vars /\ WF_vars(WorkStep) /\ SF_vars(IdleStep)

Invariant1 ==
    /\ TypeOK
    /\ \A c \in marked : Succ(c) \subseteq (marked \cup frontier)

Invariant2 ==
    marked \cup ReachFrom(frontier, Succ) = ReachFrom(marked \cup frontier, Succ)

Invariant3 ==
    ReachFrom({Root}, Succ) = marked \cup ReachFrom(frontier, Succ)

Invariants == Invariant1 /\ Invariant2 /\ Invariant3

TerminationOK == (pc = "done") => (marked = ReachFrom({Root}, Succ))

====