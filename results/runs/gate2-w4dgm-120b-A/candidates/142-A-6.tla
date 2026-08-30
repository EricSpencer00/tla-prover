---- MODULE ReachableProofs ----
EXTENDS MisraSeq, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "working"

Explore(n) ==
  /\ pc = "working"
  /\ n \in marked
  /\ \E m \in Nodes:
       /\ m \notin marked
       /\ m \notin frontier
       /\ successor(n) = m
       /\ frontier' = frontier \cup {m}
  /\ UNCHANGED <<marked, pc>>

Mark(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

FrontierEmpty ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes: Explore(n)
  \/ \E n \in Nodes: Mark(n)
  \/ FrontierEmpty

Spec == Init /\ [][Next]_vars
        /\ \A n \in Nodes: WF_vars(Explore(n)) /\ WF_vars(Mark(n))

\* Inductive: type correctness plus closure of the marked set under successors.
Invariant1 == TypeOK /\ \A n \in marked: successor(n) \in marked \cup frontier

\* Reachable-from distributes over the boundary of the marked set (Lemma 1).
Invariant2 == reachableFrom(marked) \cup reachableFrom(frontier) = reachableFrom(marked \cup frontier)

\* Reachables are exactly the marked set plus whatever the frontier yields (Lemma 2).
Invariant3 == reachableFrom(Root) = marked \cup reachableFrom(frontier)

\* Partial correctness: at termination the marked set is exactly the reachable set.
TerminationClaim == (pc = "done") => (marked = reachableFrom(Root))

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == TerminationClaim
====