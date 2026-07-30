---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The frontier may overlap with the marked set, so picking a marked node
\* simply removes it from the frontier rather than being a no-op.
Explore ==
  /\ frontier # {}
  /\ pc = "running"
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ UNCHANGED pc

AllFinished ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ AllFinished

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

\* Every successor of a marked node is either already marked or waiting in the frontier.
Inv1 ==
  \A x \in marked : \A y \in Succ[x] : y \in marked \/ y \in frontier

\* The union of marked and frontier reaches exactly the same set as the union
\* of those two sets taken as a whole.
Inv2 ==
  (marked \cup frontier) \cup
    (UNION { Succ[x] : x \in frontier }) =
  reachableFromSet(marked \cup frontier)

\* The reachable set from the root consists of the marked nodes plus whatever
\* the current frontier can still reach.
Inv3 ==
  reachableFromSet({Root}) = marked \cup reachableFromSet(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = reachableFromSet({Root}))

Termination ==
  (pc = "running") ~> (pc = "done")

\* Reachable-from-a-set closure, defined from scratch so the .cfg override
\* of the standard Seq operator does not change the model.
reachableFromSet(S) ==
  LET f[T \in SUBSET Nodes] ==
        IF T = {} THEN {}
        ELSE
          LET x == CHOOSE y \in T : TRUE
              R == Succ[x]
          IN {x} \cup reachableFromSet(R) \cup f[T \ {x}]
  IN f[S]

\* The .cfg replaces Succ, so this operator is what it actually substitutes
\* in (the name on the left is the overridden one, the name on the right is
\* what the model really uses, and both must be present).
ConnectedToSomeButNotAll(n) == Succ[n]

\* The .cfg replaces the infinite Seq operator with a bounded version.
LimitedSeq(n) == IF n < 1 THEN <<>> ELSE <<n>>

===============================================================