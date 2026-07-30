---- MODULE ReachableProofs ----
EXTENDS Integers, Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "saturating", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Saturate ==
  /\ pc # "done"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \cup Succ(n)) \ marked
  /\ pc' = "saturating"

Finish ==
  /\ frontier = {}
  /\ pc # "done"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

InitStep == pc = "idle" /\ frontier # {}
Next == Saturate \/ Finish

Spec == Init /\ [][Next]_vars

\* Invariant 1 is the inductive type/safety check: every successor of a marked
\* node already lives in the marked set or the frontier.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

\* Lemma 1 makes the two reachable-from arguments equal.
Invariant2 ==
  /\
    (marked \cup ReachableFrom(frontier))
      = ReachableFrom(marked \cup frontier)
  /\ (marked \cup frontier) \cup ReachableFrom(marked \cup frontier)
        = Nodes

\* Lemma 2 and Lemma 3 together give the third invariant.
Invariant3 == ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

TerminationPartialCorrectness ==
  /\ pc = "done"
  /\ ReachableFrom(Root) = marked

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == TerminationPartialCorrectness
====