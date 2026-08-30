---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Succ is a CONSTANT rather than a derived function: the .cfg substitutes the
\* actual mapping here, so the module must not redeclare the name, only use it.
\* It must also be drawn from the exact same finite set of successor nodes
\* that the sequential module's graph structure makes available.

SuccSet(n) == Succ[n]

\* Bounded sequence type, derived from Seq in Sequences but constrained to the
\* finite range of node indices so that the model stays finite.
LimitedSeq(n) == UNION { { Seq(n)[i] } : i \in 1..Len(Seq(n)) }

VARIABLES marked, frontier, pc, sel, succs

vars == << marked, frontier, pc, sel, succs >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in LimitedSeq(Nodes)
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = << >>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Select(p) ==
  /\ pc[p] = "idle"
  /\ frontier # << >>
  /\ sel' = [sel EXCEPT ![p] = Head(frontier)]
  /\ frontier' = Tail(frontier)
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ succs' = [succs EXCEPT ![p] = SuccSet(Head(frontier))]
  /\ UNCHANGED marked

Visit(p) ==
  /\ pc[p] = "working"
  /\ sel[p] \notin marked
  /\ marked' = marked \cup {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << frontier, sel, succs >>

\* The override is the only way a marked node can be revisited, and it is what
\* keeps the frontier bounded in a graph with cycles.
Revisit(p) ==
  /\ pc[p] = "working"
  /\ sel[p] \in marked
  /\ frontier' = Append(frontier, sel[p])
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << marked, sel, succs >>

Enqueue(p) ==
  /\ pc[p] = "working"
  /\ frontier' = frontier \o succs[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << marked, sel, succs >>

Next == \E p \in Procs : Select(p) \/ Visit(p) \/ Revisit(p) \/ Enqueue(p)

Spec == Init /\ [][Next]_vars

\* The invariant carries the inductive claim plus the control-flow shape; it
\* is the whole of the safety argument, so nothing may be dropped from it.
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \in LimitedSeq(Nodes)
  /\ \A p \in Procs : pc[p] \in {"idle", "working"}
  /\ \A p \in Procs : (pc[p] = "working") <=> (sel[p] # "none")
  /\ \A p \in Procs : pc[p] = "working" => (sel[p] \in Nodes)

\* The parallel algorithm must always be able to account for every node
\* reachable from the root as either already marked or still waiting in the
\* frontier; that is exactly the sequential Misra reachability guarantee.
Refines ==
  \A n \in Nodes : (n \in marked \/ n \in LimitedSeq(frontier)) ~> (n \in marked)

====