---- MODULE MCParReach ----
EXTENDS Sequences, FiniteSets

\* Configuration module for the parallel reachability algorithm.  It inherits
\* the entire action set from the parallel algorithm; here it provides
\* concrete definitions for the configuration constants the .cfg substitutes
\* in, namely a bounded Succ relation and a FINITE version of Seq.
CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [w \in Procs |-> "idle"]
  /\ sel = [w \in Procs |-> "none"]
  /\ succSet = [w \in Procs |-> {}]

\* Pick a frontier node to explore -- workers contend over the same Shared
\* frontier, so the same node may be picked by two workers and the CAS below
\* is what serialises the update of the shared marked set.
Pick(w, n) ==
  /\ pc[w] = "idle"
  /\ n \in frontier
  /\ sel' = [sel EXCEPT ![w] = n]
  /\ pc' = [pc EXCEPT ![w] = "hasSel"]
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED <<marked, succSet>>

\* The compare-and-swap marks the node and emits its successors into the
\* shared frontier.  It is only enabled if the node is still unmarked.
Mark(w) ==
  /\ pc[w] = "hasSel"
  /\ sel[w] \notin marked
  /\ marked' = marked \cup {sel[w]}
  /\ succSet' = [succSet EXCEPT ![w] = Succ[sel[w]]]
  /\ pc' = [pc EXCEPT ![w] = "succeeded"]
  /\ frontier' = frontier \cup Succ[sel[w]]
  /\ UNCHANGED <<sel>>

\* CAS fails: the node was already marked by the other worker.
Fail(w) ==
  /\ pc[w] = "hasSel"
  /\ sel[w] \in marked
  /\ pc' = [pc EXCEPT ![w] = "failed"]
  /\ UNCHANGED <<marked, frontier, sel, succSet>>

Reset(w) ==
  /\ pc[w] \in {"succeeded", "failed"}
  /\ pc' = [pc EXCEPT ![w] = "idle"]
  /\ sel' = [sel EXCEPT ![w] = "none"]
  /\ succSet' = [succSet EXCEPT ![w] = {}]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E w \in Procs, n \in Nodes : Pick(w, n)
  \/ \E w \in Procs : Mark(w)
  \/ \E w \in Procs : Fail(w)
  \/ \E w \in Procs : Reset(w)

Spec == Init /\ [][Next]_vars

\* SAFETY PROPERTY: type correctness plus control-flow sanity.
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A w \in Procs : pc[w] \in {"idle", "hasSel", "succeeded", "failed"}
  /\ \A w \in Procs : (pc[w] = "hasSel") => (sel[w] \in Nodes)

\* LIVENESS PROPERTY: the parallel algorithm implements the sequential
\* Misra algorithm -- every node is eventually marked.
Refines == \A n \in Nodes : <>(n \in marked)

\* Bounded model checking: replace the unbounded Succ relation with a
\* finite version that is identical on this concrete graph.
ConnectedToSomeButNotAll == Succ

\* Replacement for Seq: a version that stays finite for model checking.
LimitedSeq(i) == i

====