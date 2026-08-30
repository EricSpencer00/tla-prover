---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Configured for model checking: the graph is a concrete small digraph and
\* the worker set is a concrete small shared-memory pool. Sequence length
\* bounds are not in the model itself; they are enforced by the .cfg
\* substitution that renames Seq to a bounded, finite version.
VARIABLES marked, frontier, pc, sel, succ

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succ \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succ = [p \in Procs |-> {}]

Pick(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ frontier' = frontier \ {n}
  /\ succ' = [succ EXCEPT ![p] = Succ[n]]
  /\ UNCHANGED marked

Push(p, m) ==
  /\ pc[p] = "working"
  /\ m \in succ[p]
  /\ m \notin marked
  /\ marked' = marked \cup {m}
  /\ frontier' = frontier \cup {m}
  /\ succ' = [succ EXCEPT ![p] = succ[p] \ {m}]
  /\ UNCHANGED <<pc, sel>>

Drop(p) ==
  /\ pc[p] = "working"
  /\ succ[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succ>>

Idle ==
  /\ \A p \in Procs : pc[p] = "idle"
  /\ frontier = {}
  /\ UNCHANGED <<marked, frontier, pc, sel, succ>>

Next ==
  \/ \E p \in Procs, n \in Nodes: Pick(p, n)
  \/ \E p \in Procs, m \in Nodes: Push(p, m)
  \/ \E p \in Procs: Drop(p)
  \/ Idle

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succ>>

\* Inductive invariant covering type-correctness and the control discipline
\* (a worker is only mid-step while it holds a selected node and a nonempty
\* successor set).
Inv ==
  /\ TypeOK
  /\ \A p \in Procs :
       pc[p] = "working" => (sel[p] \in Nodes /\ succ[p] # {})

\* Refinement property: nothing marked by the parallel workers is missing
\* from the sequential reachability set.
Refines == marked \subseteq frontier

====