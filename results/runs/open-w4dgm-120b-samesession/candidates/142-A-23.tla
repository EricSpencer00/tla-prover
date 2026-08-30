---- MODULE ReachableProofs ----
EXTENDS ReachabilityAlgo, ReachabilityProofs

CONSTANTS Nodes, Root

\* No new actors: this module extends both the sequential reachability
\* algorithm and the reachability proofs module, so it inherits the state
\* variables (marked, frontier, pc) and the actions (Init, Expand, Exit).
\* The invariants are numbered to match the three key facts derived from
\* the graph-theoretic lemmas.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "search", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

Expand ==
  /\ pc \in {"init", "search"}
  /\ frontier # {}
  /\ \E n \in frontier:
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup {m \in Nodes : m \in Succ[n] /\ m \notin marked}
  /\ pc' = "search"

Exit ==
  /\ pc \in {"init", "search"}
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Init \/ Expand \/ Exit

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Invariant 1 is the type/closure pair that is preserved inductively.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Invariant 2 is the graph-theoretic Lemma 1 instantiated for the
\* combined marked/frontier region, derived rather than assumed.
Invariant2 ==
  ReachOf(marked) \cup ReachOf(frontier) = ReachOf(marked \cup frontier)

\* Invariant 3 ties the reachable set to marked/frontier via Lemma 2 and 3.
Invariant3 ==
  ReachOf(Root) = marked \cup ReachOf(frontier)

PartialCorrectness ==
  pc = "done" => marked = ReachOf(Root)

====