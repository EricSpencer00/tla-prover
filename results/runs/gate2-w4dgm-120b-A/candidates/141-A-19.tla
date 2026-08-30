---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

SuccN == Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN
         {x} \cup (SuccN[x] \cup ReachFrom(S \ {x}))

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "terminated"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore ==
    /\ frontier # {}
    /\ \E n \in frontier :
        IF n \in marked
        THEN frontier' = frontier \ {n}
        ELSE /\ marked' = marked \cup {n}
             /\ frontier' = frontier \cup SuccN[n]
    /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ pc' = "terminated"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

Inv1 ==
    \A n \in marked : (SuccN[n] \ {n}) \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    /\ Inv1
    /\ Inv2
    /\ Inv3

Termination ==
    \A n \in Nodes : (n \in ReachFrom({Root}) ~> (n \in marked)

\* The .cfg overrides Succ with ConnectedToSomeButNotAll and Seq with LimitedSeq.
\* Both are defined here so the module parses on its own.
ConnectedToSomeButNotAll(n) == SuccN[n]

LimitedSeq ==
    [x \in Seq(Naturals) |-> x]

====