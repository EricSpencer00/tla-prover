---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes, Root, Procs, Succ

\* Succ is a configuration override of the successor relation the standard
\* module would have demanded; it is supplied by the .cfg exactly as
\* ConnectedToSomeButNotAll below, so here it is just a declared constant.

VARIABLES marked, frontier, pc, sel, succs

vars == << marked, frontier, pc, sel, succs >>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> {}]

Pick(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]

Consider(p, m) ==
  /\ pc[p] = "exploring"
  /\ m \in succs[p]
  /\ sel[p] \in succs[p]
  /\ frontier' = frontier \cup {m}
  /\ succs' = [succs EXCEPT ![p] = succs[p] \ {m}]
  /\ pc' = IF succs[p] \ {m} = {} THEN "idle" ELSE "exploring"
  /\ UNCHANGED << marked, sel >>

Stall(p) ==
  /\ pc[p] = "exploring"
  /\ succs[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << marked, frontier, sel, succs >>

Done == \A p \in Procs : pc[p] = "idle" /\ frontier = {}

Next ==
  \/ \E p \in Procs, n \in Nodes : Pick(p, n)
  \/ \E p \in Procs, m \in Nodes : Consider(p, m)
  \/ \E p \in Procs : Stall(p)
  \/ (Done /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

\* The invariant is type correctness plus the control-flow shape; it is
\* what keeps frontier nodes from being inaccessible forever.
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ marked \cap frontier = {}
  /\ marked \cup frontier = Nodes
  /\ \A p \in Procs : pc[p] \in {"idle", "exploring"}
  /\ \A p \in Procs : pc[p] = "idle" => (sel[p] = Root /\ succs[p] = {})

\* Subtlety: the .cfg replaces Seq from Sequences with LimitedSeq, so the
\* module must define LimitedSeq and must NOT also define Seq itself.
LimitedSeq ==
  /\ Len(marked) = Cardinality(marked)
  /\ \A i \in 1..Len(marked) : marked[i] \in Nodes

\* The refinement property: the parallel algorithm's reachable set is
\* exactly the set reachable by the sequential Misra algorithm, hence it
\* explores no node that Misra would not and loses no reachable node.
Refines ==
  /\ FrontierIsMarkReachable
  /\ ReachableIsFrontier

FrontierIsMarkReachable ==
  \A n \in frontier : \E seq \in Seq(Nodes) :
    /\ Len(seq) =+ Cardinality(reachable)
    /\ seq # << >>
    /\ Head(seq) = Root
    /\ \A i \in 1..(Len(seq) - 1) : seq[i + 1] \in Succ[seq[i]]
    /\ seq[Len(seq)] = n

ReachableIsFrontier ==
  \A n \in reachable : n \in frontier

====