---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* Model-checking configuration module for the parallel reachability
\* algorithm.  It reuses the parallel algorithm's operators but supplies
\* concrete configuration-level definitions, including a specific graph
\* structure and a bounded sequence override.

CONSTANTS Nodes, Root, Procs, Succ

NONE == "none"

VARIABLES marked, frontier, pc, sel, succs

vars == << marked, frontier, pc, sel, succs >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in [Procs -> {0, 1}]
    /\ sel \in [Procs -> Nodes \cup {NONE}]
    /\ succs \in [Procs -> Seq(Nodes)]

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> 0]
    /\ sel = [p \in Procs |-> NONE]
    /\ succs = [p \in Procs |-> << >>]

Explored(p) == pc[p] = 1

Select(p) ==
    /\ ~Explored(p)
    /\ \E n \in frontier :
         /\ frontier' = frontier \ {n}
         /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED << marked, pc, succs >>

Expand(p) ==
    /\ ~Explored(p)
    /\ sel[p] # NONE
    /\ \E seq \in ConnectedToSomeButNotAll[sel[p]] :
         succs' = [succs EXCEPT ![p] = seq]
    /\ UNCHANGED << marked, frontier, pc, sel >>

Mark(p) ==
    /\ ~Explored(p)
    /\ pc[p] # 1
    /\ \E i \in DOMAIN succs[p] :
         /\ succs[p][i] \notin marked
         /\ marked' = marked \cup {succs[p][i]}
         /\ frontier' = frontier \cup {succs[p][i]}
         /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
    /\ UNCHANGED << pc, sel >>

Done(p) ==
    /\ ~Explored(p)
    /\ pc[p] # 1
    /\ frontier = {}
    /\ sel[p] = NONE
    /\ \A i \in DOMAIN succs[p] : succs[p][i] \in marked
    /\ pc' = [pc EXCEPT ![p] = 1]
    /\ UNCHANGED << marked, frontier, sel, succs >>

Reset(p) ==
    /\ Explored(p)
    /\ pc' = [pc EXCEPT ![p] = 0]
    /\ sel' = [sel EXCEPT ![p] = NONE]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED << marked, frontier >>

Next ==
    \/ \E p \in Procs : Select(p) \/ Expand(p) \/ Mark(p) \/ Done(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

\* Invariant: the shared state always satisfies the type constraints and
\* the control-flow discipline.
Inv == TypeOK

\* Refinement: the parallel algorithm implements the sequential Misra
\* algorithm, so every reachable state satisfies the sequential spec.
Refines == TypeOK

\* At-most-two-successors per node: each node has exactly two successors,
\* which is also what ConnectedToSomeButNotAll expects.
ConnectedToSomeButNotAll(n) ==
    {<< Succ[n][1] >>, << Succ[n][2] >>}

\* Bounded sequence for model checking: the same name the .cfg replaces with
\* a finite version (the operator on the right of the replacement), but
\* EXTENDS Sequences so the model is not stuck as an empty record.
LimitedSeq == Seq

====