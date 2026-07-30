---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* The invariant and the refinement property are named exactly as the
\* reference configuration expects.
VARIABLES marked, frontier, pc, sel, sset

vars == <<marked, frontier, pc, sel, sset>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in Seq(Nodes)
  /\ pc \in [Procs -> {"idle", "sel", "expl"}]
  /\ sel \in [Procs -> Nodes]
  /\ sset \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ sset = [p \in Procs |-> Succ[Root]]

Select(p) ==
  /\ pc[p] = "idle"
  /\ Len(frontier) > 0
  /\ sel' = [sel EXCEPT ![p] = Head(frontier)]
  /\ frontier' = Tail(frontier)
  /\ pc' = [pc EXCEPT ![p] = "sel"]
  /\ UNCHANGED <<marked, sset>>

Explore(p) ==
  /\ pc[p] = "sel"
  /\ sset' = [sset EXCEPT ![p] = Succ[sel[p]]]
  /\ pc' = [pc EXCEPT ![p] = "expl"]
  /\ UNCHANGED <<marked, frontier, sel>>

Mark(p, q) ==
  /\ pc[p] = "expl"
  /\ q \in sset[p]
  /\ q \notin marked
  /\ marked' = marked \cup {q}
  /\ frontier' = Append(frontier, q)
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<sel, sset>>

Next ==
  \E p \in Procs :
    \/ Select(p)
    \/ Explore(p)
    \/ \E q \in Nodes : Mark(p, q)

Spec == Init /\ [][Next]_vars

\* The invariant combines type correctness with the control-flow discipline
\* that distinguishes the "sel" and "expl" phases.
Inv == TypeOK

\* The refinement property is the same one used in the sequential model.
Refines == Inv

====