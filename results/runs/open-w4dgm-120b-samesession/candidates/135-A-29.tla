---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* The config overrides Succ with a bounded connective for model checking.
ConnectedToSomeButNotAll == Succ

\* Succ got replaced by ConnectedToSomeButNotAll, so Succ itself is not
\* defined here; it is the symbol the .cfg substitutes into the spec.

\* The .cfg also replaces Seq with LimitedSeq so the path quantification is
\* finite. Keep the name override out of this module's exported symbols.
LimitedSeq == Seq

VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

Start ==
  /\ pc = "idle"
  /\ pc' = "working"
  /\ UNCHANGED <<marked, frontier>>

MarkAndExpand(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup ConnectedToSomeButNotAll[n]) \ {n}
  /\ UNCHANGED pc

Idle ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Restart ==
  /\ pc = "done"
  /\ marked' = {}
  /\ frontier' = {Root}
  /\ pc' = "idle"

Next == Start \/ Idle \/ Restart \/ \E n \in Nodes : MarkAndExpand(n)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* No extra node is ever marked: the marked set is closed under Succ.
Inv1 == \A n \in Nodes : n \in marked => ConnectedToSomeButNotAll[n] \subseteq marked

\* Nothing in frontier is already marked, and every unmarked node is
\* reachable via a path from some frontier node.
Inv2 ==
  /\ frontier \cap marked = {}
  /\ \A n \in Nodes \ marked :
       \E k \in 1..Cardinality(Nodes) :
         \E p \in [1..k -> Nodes] :
           /\ p[1] \in frontier
           /\ p[k] = n
           /\ \A i \in 1..(k - 1) : p[i + 1] \in ConnectedToSomeButNotAll[p[i]]

Inv3 == marked \cup frontier = Nodes

PartialCorrectness == marked = Nodes

Termination == <>(pc = "done")
====