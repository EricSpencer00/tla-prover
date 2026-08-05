---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "looping", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

Expand ==
    /\ \E c \in frontier :
        /\ c \notin marked
        /\ marked' = marked \cup {c}
        /\ frontier' = frontier \cup Succ[c]
    /\ pc' = "looping"

Prune ==
    /\ \E c \in frontier :
        /\ c \in marked
        /\ frontier' = frontier \ {c}
    /\ pc' = "looping"

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Exploring == Expand \/ Prune \/ Terminate

Next ==
    /\ Exploring
    /\ UNCHANGED <<pc>>

Spec == Init /\ [][Exploring]_vars

Inv1 == \A c \in marked : Succ[c] \subseteq (marked \cup frontier)
Inv2 == (marked \cup frontier) \subseteq ReachableFrom(marked \cup frontier)
Inv3 == ReachableFrom(Root) = (marked \cup ReachableFrom(frontier))
PartialCorrectness == pc = "done" => marked = ReachableFrom(Root)

Termination ==
    /\ FrontierIsFinite == FiniteSet(ReachableFrom(Root))
    /\ FrontierIsFinite => (pc = "looping" ~> pc = "done")

ReachableFrom(S) ==
    LET Rec(S) ==
        IF S = {} THEN {}
        ELSE LET c == CHOOSE e \in S : TRUE IN Succ[c] \cup Rec(S \ {c})
    IN Rec(S)

FiniteSet(S) == \E n \in Nat : \E seq \in Seq(Nodes) : Cardinality(S) = n
=============================================================================