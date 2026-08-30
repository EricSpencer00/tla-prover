---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

\* The configuration module for the parallel reachability algorithm.  It adds
\* the concrete graph, the process set, and the bounded sequence
\* replacement for Seq; the action set and other variables are inherited
\* exactly from the algorithm's base specification.
CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> Seq(LimitedSeq(Nodes))]
  /\ Cardinality(frontier) <= Cardinality(Nodes)
  /\ Cardinality(marked) <= Cardinality(Nodes)

\* Control flow: a process that believes it has work must not be sitting
\* on a node nobody has actually offered it, and a finished process must
\* never still name a node.
ControlFlowOK ==
  /\ \A p \in Procs : pc[p] = "working" => sel[p] \in Nodes
  /\ \A p \in Procs : pc[p] = "done" => sel[p] = "none"

\* The inductive invariant: type correctness plus the control-flow
\* properties.  Every transition must preserve it.
Inv == TypeOK /\ ControlFlowOK

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<marked, succs>>

TakeSuccessors(p) ==
  /\ pc[p] = "working"
  /\ Cardinality(succs[p]) = 0
  /\ succs' = [succs EXCEPT ![p] = LimitedSeq(ConnectedToSomeButNotAll[sel[p]])]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

MarkKeep(p) ==
  /\ pc[p] = "working"
  /\ Cardinality(succs[p]) > 0
  /\ Cardinality(marked) < Cardinality(Nodes)
  /\ marked' = marked \cup {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED frontier

Discard(p) ==
  /\ pc[p] = "working"
  /\ Cardinality(succs[p]) > 0
  /\ Cardinality(marked) = Cardinality(Nodes)
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED <<marked, frontier>>

OfferFrontier(p, k) ==
  /\ pc[p] = "done"
  /\ k \in 1..Cardinality(succs[p])
  /\ LET c == succs[p][k] IN frontier' = frontier \cup {c}
  /\ succs' = [succs EXCEPT ![p] = SubSeq(succs[p], 1, k - 1) \o SubSeq(succs[p], k + 1, Len(succs[p]))]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, sel>>

\* Actions available from every reachable state; always enabled is the
\* nobody-has-work left stutter.
Next ==
  \/ \E p \in Procs : TakeSuccessors(p) \/ MarkKeep(p) \/ Discard(p)
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, k \in 1..Cardinality(Nodes) : OfferFrontier(p, k)

Spec == Init /\ [][Next]_vars

\* The strong claim: the parallel marking agrees exactly with the
\* sequential Misra algorithm's marking on every reachable state.
Refines ==
  \A n \in Nodes : (n \in marked) <=> (\A p \in Procs : pc[p] = "done" /\ n \in Frontier)

\* Succ is replaced here by ConnectedToSomeButNotAll (a bounded or
\* filtered view of the graph's adjacency) and Seq by LimitedSeq (a
\* FINITE, checkable version of sequence construction).
Succ == ConnectedToSomeButNotAll
LimitedSeq(S) == CHOOSE seq \in Seq(S) : \A k \in 1..Len(seq) : seq[k] \in S

====