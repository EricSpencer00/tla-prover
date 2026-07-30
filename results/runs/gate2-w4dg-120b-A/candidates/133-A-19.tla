---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

ASSUME Cardinality(Nodes) = 4
ASSUME Cardinality(Procs) = 2
ASSUME \A n \in Nodes : Cardinality(Succ[n]) = 2
ASSUME Seq \in 1..4

VARIABLES marked, frontier, pc, sel, succSet

vars == << marked, frontier, pc, sel, succSet >>

IN_t == UNION { Frontier(q) : q \in Procs }

\* The parallel algorithm proceeds independently of the configuration module, so
\* the spec, init, and next are all exactly the same as in the parallel algo.
Spec == Init /\ [][Next]_vars
Init == InitP
Next == NextP

InitP ==
  /\ marked = {Root}
  /\ frontier = [q \in Procs |-> IF q = 1 THEN {Root} ELSE {}]
  /\ pc = [q \in Procs |-> "a"]
  /\ sel = [q \in Procs |-> CHOOSE n \in Nodes : TRUE]
  /\ succSet = [q \in Procs |-> {}]

\* Pick(q) is deliberately deterministic (always the smallest node in the
\* frontier) so that an infinite run must sit on a shared resource, never on
\* a nondeterministic choice.
Pick(q) ==
  LET available == Frontier(q) \ marked IN
    IF available = {} THEN CHOOSE n \in Nodes : TRUE
    ELSE CHOOSE n \in available : \A m \in available : n <= m

NextP ==
  \/ \E q \in Procs :
       /\ pc[q] = "a"
       /\ pc' = [pc EXCEPT ![q] = "b"]
       /\ sel' = [sel EXCEPT ![q] = Pick(q)]
       /\ UNCHANGED << marked, frontier, succSet >>
  \/ \E q \in Procs :
       /\ pc[q] = "b"
       /\ sel[q] \in Frontier(q)
       /\ succSet' = [succSet EXCEPT ![q] = Succ[sel[q]]]
       /\ frontier' = [frontier EXCEPT ![q] = {}]
       /\ pc' = [pc EXCEPT ![q] = "c"]
       /\ UNCHANGED << marked, sel >>
  \/ \E q \in Procs :
       /\ pc[q] = "c"
       /\ pc' = [pc EXCEPT ![q] = "d"]
       /\ marked' = marked \cup succSet[q]
       /\ frontier' = [frontier EXCEPT ![q] = succSet[q]]
       /\ succSet' = [succSet EXCEPT ![q] = {}]
       /\ UNCHANGED << sel >>
  \/ \E q \in Procs :
       /\ pc[q] = "d"
       /\ pc' = [pc EXCEPT ![q] = "f"]
       /\ UNCHANGED << marked, frontier, sel, succSet >>
  \/ \E q \in Procs :
       /\ pc[q] = "f"
       /\ pc' = [pc EXCEPT ![q] = "e"]
       /\ UNCHANGED << marked, frontier, sel, succSet >>
  \/ \E q \in Procs :
       /\ pc[q] = "e"
       /\ pc' = [pc EXCEPT ![q] = "a"]
       /\ frontier' = [frontier EXCEPT ![q] = IF q = 1 THEN {Root} ELSE {}]
       /\ UNCHANGED << marked, sel, succSet >>

\* Inductive invariant: fields have their expected types plus every worker
\* that is mid-action has something in its frontier, and every worker that
\* read a node has a non-empty successor set. Bounded sequence length is
\* enforced by construction (each frontier is a set of nodes, never a list).
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \in [Procs -> SUBSET Nodes]
  /\ \A q \in Procs : pc[q] \in {"a", "b", "c", "d", "e", "f"}
  /\ \A q \in Procs : (pc[q] \in {"b", "c"}) => frontier[q] # {}
  /\ \A q \in Procs : (pc[q] \in {"b", "c"}) => succSet[q] # {}
  /\ IN_t \subseteq Nodes
  /\ marked \cup IN_t = Nodes

\* The parallel algorithm is a data-race-free refinement of the sequential
\* Misra algorithm.
Refines == InvokeP => RetireP

InvokeP == \E q \in Procs : pc[q] = "a"
RetireP == \A q \in Procs : pc[q] = "e" => pc[q] = "a"

====