---- MODULE MCParReach ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succs
vars == <<marked, frontier, pc, sel, succs>>

\* Every node has exactly two successors and they are always distinct, which
\* is what keeps the state space finite: the frontier can never grow without
\* an upper bound.
AllSucceed == \A n \in Nodes : Succ[n].left # Succ[n].right

NoSel == "noselect"

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..3]
  /\ sel \in [Procs -> {NoSel} \cup Nodes]
  /\ succs \in [Procs -> Seq]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> NoSel]
  /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = 0
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = succs[p] \o << Succ[n].left, Succ[n].right >>]

PopSuccessor(p, n) ==
  /\ pc[p] = 1
  /\ succs[p] # << >>
  /\ succs[p][1] = n
  /\ n \notin marked
  /\ frontier' = frontier \cup {n}
  /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<marked, sel>>

SkipMarked(p, n) ==
  /\ pc[p] = 1
  /\ succs[p] # << >>
  /\ succs[p][1] = n
  /\ n \in marked
  /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<marked, frontier, sel>>

Finish(p) ==
  /\ pc[p] = 2
  /\ sel[p] # NoSel
  /\ sel' = [sel EXCEPT ![p] = NoSel]
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<marked, frontier, succs>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, n \in Nodes : PopSuccessor(p, n)
  \/ \E p \in Procs, n \in Nodes : SkipMarked(p, n)
  \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ AllSucceed

Refines == (pc[1] = 3) <=> (Root \in marked)

====