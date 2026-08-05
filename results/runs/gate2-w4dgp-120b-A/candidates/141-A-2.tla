---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

RECURSIVE ReachOf(_, _)
ReachOf(S, X) ==
  IF X = {} THEN {}
  ELSE LET y == CHOOSE z \in X : TRUE IN
       S[y] \cup ReachOf(S, X \ {y})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

Explore ==
  \/ \E n \in frontier :
       /\ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup Succ[n]
       /\ UNCHANGED pc
  \/ \E n \in frontier :
       /\ n \in marked
       /\ frontier' = frontier \ {n}
       /\ UNCHANGED <<marked, pc>>

Next == Explore

Terminating == frontier = {}
Terminate ==
  /\ frontier = {}
  /\ pc = "run"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore) /\ Terminate

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
Inv2 ==
  ReachOf(\E n \in frontier : Succ[n], marked \cup frontier) =
    ReachOf(Succ, marked \cup frontier)
Inv3 ==
  ReachOf(Succ, {Root}) = marked \cup ReachOf(Succ, frontier)

PartialCorrectness == frontier = {} => marked = ReachOf(Succ, {Root})

Termination == frontier = {} ~> frontier = {}

RECURSIVE LimitedSeq(_)
LimitedSeq(n) == IF n = 0 THEN <<>> ELSE <<n>> \o LimitedSeq(n - 1)

Seq == LimitedSeq(3)
====