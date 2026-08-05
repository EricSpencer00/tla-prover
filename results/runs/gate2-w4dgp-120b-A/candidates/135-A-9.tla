---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Reachability algorithm with a concrete, finite graph and a bounded
\* sequence type so TLC can explore the full state space exhaustively.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Start ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "running"
  /\ UNCHANGED <<marked, frontier>>

Step(n, m) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ m \in Succ[n]
  /\ m \notin marked
  /\ marked' = marked \cup {m}
  /\ frontier' = (frontier \cup {m}) \ {n}
  /\ pc' = "running"

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Start
  \/ \E n \in Nodes, m \in Nodes : Step(n, m)
  \/ Done

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Inv1 ==
  \A n \in frontier : \E m \in marked : n \in Succ[m]

Inv2 ==
  \A u \in marked : \E s \in LimitedSeq(Nodes) :
    /\ s \in Seq(Nodes)
    /\ Len(s) > 0
    /\ s[1] = Root
    /\ s[Len(s)] = u
    /\ \A k \in 1..(Len(s) - 1) : s[k + 1] \in Succ[s[k]]

Inv3 ==
  marked = {u \in Nodes : \E s \in LimitedSeq(Nodes) :
    /\ s \in Seq(Nodes)
    /\ Len(s) > 0
    /\ s[1] = Root
    /\ s[Len(s)] = u
    /\ \A k \in 1..(Len(s) - 1) : s[k + 1] \in Succ[s[k]]}

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) <=> (\E s \in LimitedSeq(Nodes) :
    /\ s \in Seq(Nodes)
    /\ Len(s) > 0
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A k \in 1..(Len(s) - 1) : s[k + 1] \in Succ[s[k]])

Termination == <>(pc = "done")

====