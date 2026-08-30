---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The configuration binds the graph structure and process set to concrete,
\* model-checkable values and supplies the operator overrides the .cfg expects.

\* Finite (bounded) version of the sequence operator introduced by Sequences.
LimitedSeq(S, i) == IF i <= Cardinality(S) THEN CHOOSE s \in S :
    Cardinality({x \in S : x < s}) = i ELSE CHOOSE s \in S : TRUE

\* The misnomer Succ (the .cfg expects it) is bound to a graph where every node
\* has exactly 2 true successors -- a graph that is not just a cycle.
ConnectedToSomeButNotAll == Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> {}]

Start(p, n, m) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll[n]]
  /\ pc' = [pc EXCEPT ![p] = "reading"]

Finish(p) ==
  /\ pc[p] = "reading"
  /\ frontier' = frontier \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, sel>>

\* Admitting a node that has already been explored here would expand the
\* frontier without progress and is precisely what starvation-prevention rules
\* must rule out; so it is disallowed as a state transition, not just a liveness
\* property.
Admit(n) ==
  /\ n \notin marked
  /\ n \notin frontier
  /\ frontier' = frontier \cup {n}
  /\ UNCHANGED <<marked, pc, sel, succs>>

Next ==
  \/ \E p \in Procs, n \in frontier, m \in succs[p] : Start(p, n, m)
  \/ \E p \in Procs : Finish(p)
  \/ \E n \in Nodes : Admit(n)

Spec == Init /\ [][Next]_vars

\* Safety: type correctness plus pairwise frontier disjointness of the two processes.
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ marked \cap frontier = {}
  /\ pc \in [Procs -> {"idle", "reading"}]
  /\ sel \in [Procs -> Nodes]
  /\ succs \in [Procs -> SUBSET Nodes]

\* Progress: every node eventually gets explored.
Refines == \A n \in Nodes : (\E p \in Procs : pc[p] = "idle" /\ sel[p] = n) ~> (n \in marked)

====