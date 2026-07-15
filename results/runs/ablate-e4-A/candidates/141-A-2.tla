---- MODULE Reachable ----
EXTENDS Naturals, Sequences, SETS

CONSTANTS Nodes, Root, Succ, Seq

Rel == { x \in Nodes, y \in Nodes : y \in Succ[x] }

ReachableFrom(S) ==
    { y \in Nodes : \E x \in S : (x, y) \in TransitiveClosure(Rel) }

VARIABLES Marked, Frontier, pc

TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"running", "terminated"}
    /\ Root \in Nodes
    /\ Succ \in [Nodes -> SUBSET Nodes]
    /\ Seq \in Seq(Nodes)

Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "running"

PickNode ==
    /\ pc = "running"
    /\ Frontier /= {}
    /\ \E n \in Frontier :
        IF n \notin Marked THEN
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = Frontier \cup Succ[n]
          /\ pc' = "running"
        ELSE
          /\ Marked' = Marked
          /\ Frontier' = Frontier \ {n}
          /\ pc' = "running"

Terminate ==
    /\ pc = "running"
    /\ Frontier = {}
    /\ pc' = "terminated"
    /\ Marked' = Marked
    /\ Frontier' = Frontier

Stutter ==
    /\ pc = "terminated"
    /\ UNCHANGED <<Marked, Frontier, pc>>

Next == PickNode \/ Terminate \/ Stutter

Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

Inv1 ==
    \A n \in Marked : Succ[n] \subseteq Marked \cup Frontier

Inv2 ==
    Marked \cup ReachableFrom(Frontier) \subseteq ReachableFrom(Marked \cup Frontier)

Inv3 ==
    ReachableFrom(Marked \cup Frontier) \subseteq Marked \cup ReachableFrom(Frontier)

PartialCorrectness ==
    (pc = "terminated") => (Marked = ReachableFrom({Root}))

Termination == <> (pc = "terminated")

====