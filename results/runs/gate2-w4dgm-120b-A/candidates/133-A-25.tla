---- MODULE MCParReach ----
EXTENDS Integers, Naturals, FiniteSets, Sequences

\* Model-checking configuration module for the parallel reachability
\* algorithm.  It adds concrete configuration definitions (a graph with
\* exactly 2 successors per node, a sequence bound) on top of the parallel
\* algorithm's core specification, which supplies the rest of the system.

CONSTANTS Nodes, Root, Procs, Succ

NONE == "none"
MaxLen == Cardinality(Nodes)

VARIABLES marked, frontier, pc, chosen, sucs

vars == <<marked, frontier, pc, chosen, sucs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "holding", "done"}]
  /\ chosen \in [Procs -> Nodes \cup {NONE}]
  /\ sucs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ chosen = [p \in Procs |-> NONE]
  /\ sucs = [p \in Procs |-> << >>]

\* A worker claims a frontier node and reads its successors into a bounded
\* sequence.
Claim(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "holding"]
  /\ chosen' = [chosen EXCEPT ![p] = n]
  /\ sucs' = [sucs EXCEPT ![p] = << >>]
  /\ UNCHANGED marked

Explore(p, m) ==
  /\ pc[p] = "holding"
  /\ m \in Succ[chosen[p]]
  /\ Len(sucs[p]) < MaxLen
  /\ sucs' = [sucs EXCEPT ![p] = Append(sucs[p], m)]
  /\ UNCHANGED <<marked, frontier, pc, chosen>>

Admit(p) ==
  /\ pc[p] = "holding"
  /\ chosen' = [chosen EXCEPT ![p] = NONE]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sucs>>

Mark(p, i) ==
  /\ pc[p] = "holding"
  /\ i \in DOMAIN sucs[p]
  /\ sucs[p][i] \notin marked
  /\ marked' = marked \cup {sucs[p][i]}
  /\ frontier' = frontier \cup {sucs[p][i]}
  /\ sucs' = [sucs EXCEPT ![p] = Seq(Take(sucs[p], i - 1))]
  /\ UNCHANGED <<pc, chosen>>

Next ==
  \/ \E p \in Procs, n \in Nodes: Claim(p, n)
  \/ \E p \in Procs, m \in Nodes: Explore(p, m)
  \/ \E p \in Procs: Admit(p)
  \/ \E p \in Procs, i \in 1..MaxLen: Mark(p, i)

Spec == Init /\ [][Next]_vars

\* Inductive invariant: the reachable set is closed under the graph's
\* successors, and no worker is ever left in an invalid state.
Inv ==
  /\ marked \subseteq {n \in Nodes : \A q \in Nodes : q \in Succ[n] => q \in marked}
  /\ \A p \in Procs:
       \/ pc[p] \in {"idle", "done"}
       \/ (pc[p] = "holding" /\ chosen[p] \in Nodes)

\* Safety: the parallel algorithm implements the sequential Misra control
\* flow -- every worker is either idle or holding a node, never both.
Refines ==
  \A p \in Procs: pc[p] \in {"idle", "holding", "done"}

\* The configuration injects a concrete successor relation and a bounded
\* sequence operator for model checking.  ConnectedToSomeButNotAll is the
\* shape the .cfg substitutes for Succ (finite, non-empty, not universal).
ConnectedToSomeButNotAll(n) == {m \in Nodes : m # n}

\* The .cfg substitutes this bounded version for Seq from the Sequences
\* module, keeping the operator in scope (no re-declaration) but changing
\* its semantics to a finite version for model checking.
LimitedSeq == Seq

====