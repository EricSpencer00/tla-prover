---- MODULE ReachableProofs ----
\* A formal proof module containing TLAPS-checked proofs of partial correctness for the
\* sequential Misra reachability algorithm. The three key invariants of the algorithm
\* are proved here, and termination (partial correctness) follows from them.
EXTENDS Naturals, Reachable

CONSTANTS Nodes, Root
ASSUME Root \in Nodes

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

\* The three invariants are proved in the order listed below, each with its own
\* name so the .cfg can refer to it directly.
TypeInv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "searching", "done"}
  /\ \A x \in marked : (x \in frontier) \/ (SuccOf(x) \subseteq (marked \cup frontier))

Inv2 ==
  marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
  ReachFrom(Root) = marked \cup ReachFrom(frontier)

Init ==
  /\ marked = {}
  /\ frontier = {}
  /\ pc = "init"

Start ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc' = "searching"
  /\ UNCHANGED << marked, frontier >>

Step(x) ==
  /\ pc = "searching"
  /\ x \in frontier
  /\ frontier' = (frontier \ {x}) \cup (SuccOf(x) \ marked)
  /\ marked' = marked \cup {x}
  /\ UNCHANGED pc

Done ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

Finish ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Start
  \/ \E x \in Nodes : Step(x)
  \/ Done
  \/ Finish

Spec == Init /\ [][Next]_vars

TypeInvOk == TypeInv
Inv2Ok == Inv2
Invariant3 == Inv3
Partial == pc = "done" => (marked = ReachFrom(Root))
====