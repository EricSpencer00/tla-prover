---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

States == {"idle", "running", "done"}

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in States

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Start ==
    /\ pc = "idle"
    /\ pc' = "running"
    /\ UNCHANGED <<marked, frontier>>

Mark(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \ {n}) \cup Succ[n]
    /\ UNCHANGED pc

Stop ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

DoneStep ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ \E n \in Nodes : Mark(n)
    \/ Stop
    \/ DoneStep

Spec == Init /\ [][Next]_vars /\ WF_vars(Stop)

Inv1 ==
    /\ frontier \subseteq Nodes
    /\ marked \cap frontier = {}
    /\ marked \cup frontier = Nodes

Inv2 ==
    \A a \in marked, b \in marked : (b \in Succ[a]) \/ (a \in Succ[b])

Inv3 ==
    \A a \in Nodes : (a \notin marked) => (a \in frontier)

PartialCorrectness ==
    \A a \in Nodes : (a \in marked) <=> (a \in frontier)

Termination == (pc = "done") ~> (pc = "done")

ConnectedToSomeButNotAll ==
    Succ

LimitedSeq ==
    Seq

====