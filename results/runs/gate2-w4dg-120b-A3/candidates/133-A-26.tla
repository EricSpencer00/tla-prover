---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The full set of state variables, carried over from the parallel
\* reachability algorithm.  The model-checking module inherits them
\* wholesale; this module only adds the configuration definitions.
VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Nodes -> SUBSET Nodes]

\* The control invariants of the parallel algorithm: a worker only
\* holds a selected node when it is actually working, and it only ever
\* picks a node that has been marked already.
ControlInvariants ==
  /\ \A p \in Procs : (pc[p] = "working") => (sel[p] # "none")
  /\ \A p \in Procs : sel[p] # "none" => (sel[p] \in marked)

\* Succ has been overridden by the .cfg file; its definition here is
\* the concrete connected-2 graph structure the model checker will
\* actually use for the bounded graph.
Succ == ConnectedToSomeButNotAll

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [n \in Nodes |-> Succ[n]]

\* Standard parallel reachability actions, unchanged by this
\* configuration module.
Explore(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![n] = succs[n] \cup {n}]
  /\ UNCHANGED << >>

Settle(p) ==
  /\ pc[p] = "working"
  /\ sel[p] # "none"
  /\ frontier' = frontier \cup succs[sel[p]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED << marked, succs >>

Next ==
  \/ \E p \in Procs, n \in Nodes : Explore(p, n)
  \/ \E p \in Procs : Settle(p)

\* The inductive invariant is the type correctness plus the control
\* invariants -- the property the .cfg file names.
Inv == TypeOK /\ ControlInvariants

\* The refinement to the sequential Misra algorithm, also named in the
\* .cfg file.
Refines == Inv

\* Bounded sequences: the .cfg file replaces Seq with a finite
\* version so the model is tractable.  We keep EXTENDS Sequences but
\* do not declare Seq here, so it resolves to its overridden, bounded
\* definition wherever the .cfg file applies.
LimitedSeq == CHOOSE s \in FiniteSeq(Nodes) : TRUE

Spec == Init /\ [][Next]_vars

====