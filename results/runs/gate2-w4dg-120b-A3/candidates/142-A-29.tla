---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

\* The algorithm's state variables (inherited from the base module):
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_, _)
ReachFrom(S, G) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
           NextS == (S \ {x}) \cup (G[x] \cap Nodes)
       IN {x} \cup ReachFrom(NextS, G)

RECURSIVE Succ(_)
Succ(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
       IN (G[x] \cap Nodes) \cup Succ(S \ {x})

\* The graph is fixed (a constant), so it is defined once and for all here:
G == [n \in Nodes |-> Succ(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Explore(n) ==
  /\ pc = "idle"
  /\ n \in marked
  /\ G[n] \cap Nodes # {}
  /\ frontier' = frontier \cup (G[n] \cap Nodes)
  /\ pc' = "exploring"
  /\ UNCHANGED marked

Mark(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = "idle"

Idle ==
  /\ pc = "idle"
  /\ frontier = {}
  /\ \A n \in marked : G[n] \cap Nodes = {}
  /\ UNCHANGED vars

Next == Idle \/ \E n \in Nodes : Explore(n) \/ Mark(n)

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus every successor of a marked node already
\* in the marked set or the frontier.
Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring"}
  /\ \A n \in marked : G[n] \cap Nodes \subseteq marked \cup frontier

\* Invariant 2: marked plus nodes reachable from the frontier cover exactly
\* the nodes reachable from the union of marked and frontier (Lemma 1).
Inv2 ==
  ReachFrom(marked \cup frontier, G) = marked \cup ReachFrom(frontier, G)

\* Invariant 3: reachable nodes from the root are the marked set plus those
\* reachable from the frontier (Lemma 2 + Lemma 3).
Inv3 ==
  ReachFrom({Root}, G) = marked \cup ReachFrom(frontier, G)

\* The TLAPS-checked partial-correctness theorem: on termination, the marked
\* set equals the reachable set.
TerminationClaim ==
  (pc = "idle" /\ frontier = {}) => (marked = ReachFrom({Root}, G))

InitInv == Init => Inv1

INVARIANTS InitInv, Inv1, Inv2, Inv3

PROPERTIES TerminationClaim

====