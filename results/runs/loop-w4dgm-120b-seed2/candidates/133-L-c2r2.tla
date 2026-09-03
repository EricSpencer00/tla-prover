---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The model replaces Succ with a version that bounds each sequence, and
\* replaces Seq with a finite version; the overrides are declared here and
\* are the only thing the .cfg file changes about this module.
ConnectedToSomeButNotAll == Succ

LimitedSeq(a) == CHOOSE s \in Sequences.Seq : s \in Sequences.FinSeq /\ s \in a

NoneP == "none"
AllDone == "done"

VARIABLES marked, frontier, pc, chosen, succs

vars == << marked, frontier, pc, chosen, succs >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {NoneP, AllDone} \cup (1..3)]
  /\ chosen \in [Procs -> Nodes \cup {NoneP}]
  /\ succs \in [Procs -> Sequences.Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> NoneP]
  /\ chosen = [p \in Procs |-> NoneP]
  /\ succs = [p \in Procs |-> LimitedSeq(@)]

\* Pick an unmarked node and read its successors into a bounded sequence.
Pick(p, n) ==
  /\ pc[p] = NoneP
  /\ n \notin marked
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ chosen' = [chosen EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = LimitedSeq(ConnectedToSomeButNotAll[n])]
  /\ UNCHANGED << marked, frontier >>

\* Add the next successor that has not been explored yet.
Add(p) ==
  /\ pc[p] = 1
  /\ Len(succs[p]) > 0
  /\ LET m == Head(succs[p]) IN
       /\ m \notin marked
       /\ marked' = marked \cup {m}
       /\ frontier' = frontier \cup {m}
       /\ succs' = [succs EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED << pc, chosen >>

\* Discard a successor that is already marked; keep scanning.
Skip(p) ==
  /\ pc[p] = 1
  /\ Len(succs[p]) > 0
  /\ Head(succs[p]) \in marked
  /\ succs' = [succs EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED << marked, frontier, pc, chosen >>

Done(p) ==
  /\ pc[p] = 1
  /\ Len(succs[p]) = 0
  /\ pc' = [pc EXCEPT ![p] = AllDone]
  /\ UNCHANGED << marked, frontier, chosen, succs >>

Reset(p) ==
  /\ pc[p] = AllDone
  /\ pc' = [pc EXCEPT ![p] = NoneP]
  /\ chosen' = [chosen EXCEPT ![p] = NoneP]
  /\ succs' = [succs EXCEPT ![p] = LimitedSeq(@)]
  /\ UNCHANGED << marked, frontier >>

Explore(p) == \E n \in Nodes : Pick(p, n)

Next ==
  \/ \E p \in Procs : Explore(p) \/ Add(p) \/ Skip(p) \/ Done(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

\* The workers never lose or fabricate data: every chosen node is a real
\* node, every frontier node is marked, and the bounded sequences never
\* grow past the size of the reachable region -- the last bit is the
\* finite bound the .cfg file relies on.
Inv ==
  /\ \A p \in Procs : chosen[p] \in Nodes \cup {NoneP}
  /\ frontier \subseteq marked
  /\ \A p \in Procs : Len(succs[p]) <= Cardinality(Nodes)

\* The parallel algorithm never explores more (and never less) than the
\* sequential Misra algorithm: its marked set is exactly the reachable
\* region of the graph, not a strict superset or subset of it.
Refines ==
  marked = {n \in Nodes : \E k \in 0..Cardinality(Nodes) : Reachable(k, n)}
====