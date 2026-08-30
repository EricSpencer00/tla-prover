---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* The reachable-from relation, built from the graph's successor relation.
RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE x \in S : TRUE IN Succ[n] \cup ReachFrom(S \ {n})

ReachRoot == ReachFrom({Root})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "halted"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The overlap is intentional: a node may sit in frontier while already marked.
Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ IF n \notin marked
          THEN /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
          ELSE /\ marked' = marked
               /\ frontier' = frontier \ {n}
  /\ pc' = pc

Halt ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "halted"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Halt

Spec == Init /\ [][Next]_vars

\* Nodes reachable from any marked node are either already marked or still
\* waiting in the frontier; together they account for everything reachable.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
Inv2 == ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)
Inv3 == ReachRoot = marked \cup ReachFrom(frontier)

PartialCorrectness == ReachRoot = marked

Terminate == (Frontier = {}) ~> (Pc = "halted")

Frontier == frontier
Pc == pc

\* The .cfg overrides Succ with a bounded version; keep the operator here.
ConnectedToSomeButNotAll == {n \in Nodes : Succ[n] # {}}

\* The .cfg replaces Seq with a finite version; keep its definition here.
LimitedSeq == Sequences.FinSeq
====