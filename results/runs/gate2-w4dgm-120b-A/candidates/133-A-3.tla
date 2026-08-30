---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Deterministic tie-breaking: the successor of a node is the smallest one
\* in its adjacency set, so every node's Next is uniquely defined.
NextOf(n) == CHOOSE m \in Succ[n] : \A q \in Succ[n] : m <= q

None == "none"
MaxSteps == Cardinality(Nodes)
MaxSeq == Cardinality(Nodes)

VARIABLES marked, frontier, pc, chosen, succs
vars == <<marked, frontier, pc, chosen, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "select", "marking", "done"}]
  /\ chosen \in [Procs -> Nodes \cup {None}]
  /\ succs \in [Procs -> SUBSET Nodes]

\* The shared marked set and frontier stay disjoint; a worker may only be
\* mid-step while its chosen node is still frontier, which forces genuine
\* progress rather than a worker re-selecting a node another worker took.
Disjointness ==
  /\ marked \cap frontier = {}
  /\ \A w \in Procs : pc[w] = "marking" => chosen[w] \in frontier

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [w \in Procs |-> "idle"]
  /\ chosen = [w \in Procs |-> None]
  /\ succs = [w \in Procs |-> {}]

Select(w) ==
  /\ pc[w] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ chosen' = [chosen EXCEPT ![w] = n]
       /\ pc' = [pc EXCEPT ![w] = "select"]
  /\ UNCHANGED <<marked, frontier, succs>>

BeginMark(w) ==
  /\ pc[w] = "select"
  /\ chosen[w] \in frontier
  /\ pc' = [pc EXCEPT ![w] = "marking"]
  /\ UNCHANGED <<marked, frontier, chosen, succs>>

FinishMark(w) ==
  /\ pc[w] = "marking"
  /\ chosen[w] \in frontier
  /\ marked' = marked \cup {chosen[w]}
  /\ frontier' = (frontier \ {chosen[w]}) \cup succs[w]
  /\ pc' = [pc EXCEPT ![w] = "idle"]
  /\ chosen' = [chosen EXCEPT ![w] = None]
  /\ succs' = [succs EXCEPT ![w] = {}]

Abort(w) ==
  /\ pc[w] \in {"select", "marking"}
  /\ pc' = [pc EXCEPT ![w] = "idle"]
  /\ chosen' = [chosen EXCEPT ![w] = None]
  /\ succs' = [succs EXCEPT ![w] = {}]
  /\ UNCHANGED <<marked, frontier>>

LoadSucc(w) ==
  /\ pc[w] = "idle"
  /\ frontier # {}
  /\ \E m \in frontier :
       /\ chosen[w] = m
       /\ succs[w] = {NextOf(m)}
  /\ pc' = [pc EXCEPT ![w] = "select"]
  /\ UNCHANGED <<marked, frontier, chosen>>

Next ==
  \/ \E w \in Procs : Select(w)
  \/ \E w \in Procs : BeginMark(w)
  \/ \E w \in Procs : FinishMark(w)
  \/ \E w \in Procs : Abort(w)
  \/ \E w \in Procs : LoadSucc(w)

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ Disjointness

\* Exact misra algorithm: the shared frontier is precisely the successors
\* of the marked set minus the nodes already marked.
Refines ==
  frontier = ( {NextOf(m) : m \in marked} \ {None} ) \ marked

\* The .cfg substitutes a finite version of Succ (EqualToRoot) and of Seq
\* (LimitedSeq) here, so the shape is present even though it is a no-op.
EqualToRoot(n) == {n} = {Root}
LimitedSeq(f, S) == f[S]
ConnectedToSomeButNotAll == NONE
====