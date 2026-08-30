---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

N == Cardinality(Nodes)

\* The worker set is inherited from the parallel-reachability spec; it
\* must be a distinct constant here so the .cfg override can name it.
Workers == Procs

VARIABLES marked, frontier, pc, chosen, succ

Vars == <<marked, frontier, pc, chosen, succ>>

\* Succ is a constant function naming each node's two successors in the graph.
\* The model bounds its range to nodes in the same fixed graph (never expands).
\* ConnectedToSomeButNotAll is the .cfg substitution for Succ in formulas.
ConnectedToSomeButNotAll(n) == Succ[n]

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Workers -> {"idle", "spinning", "working", "crashed"}]
  /\ chosen \in [Workers -> Nodes \cup {"none"}]
  /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [w \in Workers |-> "idle"]
  /\ chosen = [w \in Workers |-> "none"]
  /\ succ = Succ

Pick(w, n) ==
  /\ pc[w] = "idle"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![w] = "spinning"]
  /\ chosen' = [chosen EXCEPT ![w] = n]
  /\ succ' = [succ EXCEPT ![n] = ConnectedToSomeButNotAll(n)]

\* The non-deterministic spin that may repeatedly fail before it wins; nothing
\* is ever written here, only a guarded action.
Spin(w) ==
  /\ pc[w] = "spinning"
  /\ pc' = [pc EXCEPT ![w] = "working"]
  /\ UNCHANGED <<marked, frontier, chosen, succ>>

Visit(w) ==
  /\ pc[w] = "working"
  /\ frontier' = frontier \cup succ[chosen[w]]
  /\ succ' = [succ EXCEPT ![chosen[w]] = {}]
  /\ pc' = [pc EXCEPT ![w] = "idle"]
  /\ chosen' = [chosen EXCEPT ![w] = "none"]
  /\ UNCHANGED marked

Crash(w) ==
  /\ pc[w] \in {"spinning", "working"}
  /\ pc' = [pc EXCEPT ![w] = "crashed"]
  /\ UNCHANGED <<marked, frontier, chosen, succ>>

Reclaim(w) ==
  /\ pc[w] = "crashed"
  /\ marked' = IF chosen[w] \in marked THEN marked ELSE marked \cup {chosen[w]}
  /\ frontier' = frontier \cup (IF chosen[w] \in frontier THEN {} ELSE {chosen[w]})
  /\ succ' = [succ EXCEPT ![chosen[w]] = ConnectedToSomeButNotAll(chosen[w])]
  /\ pc' = [pc EXCEPT ![w] = "idle"]
  /\ chosen' = [chosen EXCEPT ![w] = "none"]

Next ==
  \/ \E w \in Workers, n \in Nodes : Pick(w, n)
  \/ \E w \in Workers : Spin(w)
  \/ \E w \in Workers : Visit(w)
  \/ \E w \in Workers : Crash(w)
  \/ \E w \in Workers : Reclaim(w)

Spec == Init /\ [][Next]_Vars

\* The invariant is control-flow/typing sanity, not progress: it never blocks.
Inv ==
  /\ marked \cap frontier = {}
  /\ \A w \in Workers : pc[w] \in {"idle", "spinning", "working", "crashed"}
  /\ \A w \in Workers : pc[w] = "idle" => chosen[w] = "none"
  /\ \A w \in Workers : pc[w] \in {"spinning", "working"} => chosen[w] \in Nodes
  /\ \A n \in Nodes : succ[n] \subseteq Nodes

\* The refinement property: no node is ever in flight to itself, which is
\* exactly what Misra's improvement ruled out on top of the plain travel set.
Refines ==
  \A w \in Workers : chosen[w] # "none" => chosen[w] \notin succ[chosen[w]]

====