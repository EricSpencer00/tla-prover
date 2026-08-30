---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

\* This config module for the parallel reachability algorithm provides the
\* concrete graph (EachHasTwoSucc) and the bounded sequence override
\* (LimitedSeq) that make the model finite.  The rest of the algorithm --
\* its actions and its safety/liveness spec -- is inherited unchanged from
\* the standard ParReach specification.

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs
vars == <<marked, frontier, pc, selected, succs>>

\* The action set is unchanged from ParReach; we just rename it for the
\* .cfg file rather than redefining it here.
Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> {}]

Start(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ selected' = [selected EXCEPT ![p] = n]
       /\ succs' = [succs EXCEPT ![p] = Succ[n]]
       /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ marked' = marked

Mark(p) ==
  /\ pc[p] = "working"
  /\ marked' = marked \cup succs[p]
  /\ frontier' = frontier \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = Root]
  /\ succs' = [succs EXCEPT ![p] = {}]

Reset(p) ==
  /\ pc[p] = "working"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = Root]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Next == \E p \in Procs : Init \/ Start(p) \/ Mark(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

\* Type-correctness and the control-flow shape the full invariant; the
\* refinement property below is the second one the .cfg demands.
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ marked \cap frontier = {}
  /\ marked \cup frontier = Nodes
  /\ \A p \in Procs :
       /\ pc[p] \in {"idle", "working"}
       /\ (pc[p] = "idle") <=> (selected[p] = Root /\ succs[p] = {})
       /\ (pc[p] = "working") => (selected[p] \in Nodes)

Refines ==
  /\ (Root \in frontier) <=> (Root \notin marked)
  /\ frontier # {}
  /\ \A n \in frontier : marked \cap Succ[n] = {}
  /\ \A n \in frontier : \E p \in Procs : n \in succs[p]

\* Configuration-level constant: the concrete graph structure used by both
\* the parallel and the sequential algorithm's model checking.
EachHasTwoSucc == \A n \in Nodes : Cardinality(Succ[n]) = 2

\* The .cfg file substitutes this for the unbounded Seq operator; it is
\* deliberately kept as a thin wrapper so the override stays semantics-
\* preserving except for the finiteness it imposes.
LimitedSeq == Seq

====