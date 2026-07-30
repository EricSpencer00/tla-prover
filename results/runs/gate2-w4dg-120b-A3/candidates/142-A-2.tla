---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

VARIABLES rs, frontier, pc

vars == <<rs, frontier, pc>>

RECURSIVE ReachableFrom(_, _)
ReachableFrom(S, T) ==
  IF S = {} THEN T
  ELSE LET n == CHOOSE x \in S : TRUE
           rest == ReachableFrom(S \ {n}, T)
       IN IF \E m \in T : m \in rs : rest
          ELSE rest \cup {n}

Init ==
  /\ rs \in SUBSET Nodes
  /\ frontier = {}
  /\ pc = 0

Next ==
  /\ pc < 3
  /\ pc' = pc + 1
  /\ rs' = rs
  /\ frontier' = frontier

Spec ==
  /\ Init
  /\ [][Next]_vars

TypeOK ==
  /\ rs \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {0, 1, 2, 3}

Invariant1 ==
  /\ TypeOK
  /\ \A m \in rs, n \in Nodes : (m, n) \in frontier => (n \in rs \/ n \in frontier)

Invariant2 ==
  rs \cup ReachableFrom(frontier, {}) = ReachableFrom(rs \cup frontier, {})

Invariant3 ==
  ReachableFrom({Root}, {}) = rs \cup ReachableFrom(frontier, {})

PartialCorrectness ==
  /\ pc = 3
  => ReachableFrom({Root}, {}) = rs

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {PartialCorrectness}
====