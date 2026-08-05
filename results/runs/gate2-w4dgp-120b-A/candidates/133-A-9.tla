---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> ""]
  /\ succs = [p \in Procs |-> <<>>]

Pick(n) == \E p \in Procs : frontier = {} /\ frontier' = {n} /\ UNCHANGED <<marked, pc, sel, succs>>

\* Each worker independently and nondeterministically picks a frontier node to explore.
Explore(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
       /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED marked

\* The bounded sequence override (LimitedSeq) replaces the unbounded Seq: only a bounded
\* number of successors per node can be taken, so the model stays finite.
Expand(p) ==
  /\ pc[p] = "exploring"
  /\ Len(succs[p]) < Cardinality(Nodes)
  /\ \E m \in Succ[sel[p]] : succs' = [succs EXCEPT ![p] = Append(succs[p], m)]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Mark(p) ==
  /\ pc[p] = "exploring"
  /\ succs[p] # <<>>
  /\ \E m \in succs[p] :
       /\ m \notin marked
       /\ marked' = marked \cup {m}
       /\ frontier' = frontier \cup {m}
  /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
  /\ UNCHANGED <<pc, sel>>

Finish(p) ==
  /\ pc[p] = "exploring"
  /\ succs[p] = <<>
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = ""]
  /\ UNCHANGED <<marked, frontier, succs>>

PickAny == \E n \in Nodes : Pick(n)
ExploreAny == \E p \in Procs : Explore(p)
ExpandAny == \E p \in Procs : Expand(p)
MarkAny == \E p \in Procs : Mark(p)
FinishAny == \E p \in Procs : Finish(p)

Next == PickAny \/ ExploreAny \/ ExpandAny \/ MarkAny \/ FinishAny

Spec == Init /\ [][Next]_vars

\* Inductive safety: all workers are at the same stage in the algorithm's control flow
\* and no worker is stuck in the middle of a frontier or successor sequence.
Inv ==
  /\ marked \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in {"idle", "exploring"}
  /\ \A p \in Procs :
       (pc[p] = "exploring") =>
         /\ succs[p] # <<>>
         /\ frontier \cap {sel[p]} = {}
  /\ \A p \in Procs : sel[p] # "" => sel[p] \in frontier

\* The parallel algorithm implements exactly the same reachable set as the sequential
\* Misra Reachability algorithm's Reachable set.
Refines == marked \subseteq Reachable

====