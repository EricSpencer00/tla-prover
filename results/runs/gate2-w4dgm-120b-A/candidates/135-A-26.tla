---- MODULE MCReachable ----
EXTENDS FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Bounded path existential: the standard Sequences operator is overridden
\* in the .cfg file with a FINITE version called LimitedSeq, so this
\* module keeps the EXTENDS Sequences and never redeclares Seq itself.
Seq == LimitedSeq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Bump(b) == IF b = "idle" THEN "searching" ELSE "idle"
Frontiers == UNION {Succ[n] : n \in frontier}

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

StartSearch(n) ==
  /\ pc = "idle"
  /\ frontier' = {n}
  /\ pc' = Bump(pc)
  /\ UNCHANGED marked

Expand ==
  /\ frontier # {}
  /\ frontier' = Frontiers \ frontier
  /\ marked' = marked \cup Frontiers
  /\ pc' = Bump(pc)

Terminate ==
  /\ frontier = {}
  /\ pc = "searching"
  /\ pc' = Bump(pc)
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : StartSearch(n)
  \/ Expand
  \/ Terminate

Spec == Init /\ [][Next]_vars
Termination == <>(pc = "idle")

ClosureInv ==
  \A x \in frontier : Succ[x] \subseteq marked \cup frontier
ReachabilityInv ==
  \A x \in frontier :
    \E s \in Seq(Nodes) :
      /\ Len(s) >= 2
      /\ s[1] = Root
      /\ s[Len(s)] = x
      /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]
DecompositionInv ==
  \A x \in marked : \A s \in Seq(Nodes) :
    (s[1] = Root /\ s[Len(s)] = x /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]) => x \in marked
ReachableInv ==
  marked = {x \in Nodes : \E s \in Seq(Nodes) :
    /\ s[1] = Root
    /\ s[Len(s)] = x
    /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]}

Inv1 == ClosureInv
Inv2 == ReachabilityInv
Inv3 == DecompositionInv
PartialCorrectness == ReachableInv

====