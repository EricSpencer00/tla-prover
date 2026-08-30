---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* The set of configuration-level operators a model-checking run substitutes.
\* It must be kept in exact correspondence with the .cfg file that runs TLC.
\* Each line below defines the operator on the right, which the .cfg substitutes
\* for the identifier on the left wherever it occurs in the model.
CONSTANTS
    ConnectedToSomeButNotAll

\* Succ is a finite relation here, but the .cfg substitutes it with ConnectedToSomeButNotAll.
Succ == ConnectedToSomeButNotAll

SomeElem == CHOOSE n \in Nodes : TRUE
NoNode == "none"

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in Nodes \cup {NoNode}
    /\ pc \in [Procs -> {"idle", "selecting", "succs", "done"}]
    /\ sel \in [Procs -> Nodes \cup {NoNode}]
    /\ succ \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = Root
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> NoNode]
    /\ succ = [p \in Procs |-> {}]

SelectNode(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in Nodes
    /\ pc' = [pc EXCEPT ![p] = "selecting"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, frontier, succ>>

ReadSuccs(p) ==
    /\ pc[p] = "selecting"
    /\ pc' = [pc EXCEPT ![p] = "succs"]
    /\ succ' = [succ EXCEPT ![p] = Succ[sel[p]]]
    /\ UNCHANGED <<marked, frontier, sel>>

Commit(p) ==
    /\ pc[p] = "succs"
    /\ frontier # NoNode
    /\ frontier \in succ[p]
    /\ marked' = marked \cup {frontier}
    /\ frontier' = NoNode
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<sel, succ>>

\* The rendezvous: a process may only advance the frontier once both sides agree.
AdvanceFrontier(p, n) ==
    /\ pc[p] = "done"
    /\ frontier = NoNode
    /\ n \in succ[p]
    /\ frontier' = n
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = NoNode]
    /\ succ' = [succ EXCEPT ![p] = {}]
    /\ UNCHANGED marked

\* Restarts are only possible while the frontier is occupied.
Restart(p) ==
    /\ pc[p] = "done"
    /\ frontier # NoNode
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = NoNode]
    /\ succ' = [succ EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E p \in Procs : \E n \in Nodes : SelectNode(p, n)
    \/ \E p \in Procs : ReadSuccs(p)
    \/ \E p \in Procs : Commit(p)
    \/ \E p \in Procs : \E n \in Nodes : AdvanceFrontier(p, n)
    \/ \E p \in Procs : Restart(p)

Spec == Init /\ [][Next]_vars

\* The invariant is type correctness plus a control-flow discipline: a process
\* that has read successors can never be sitting in the idle state.
Inv ==
    /\ TypeOK
    /\ \A p \in Procs : pc[p] = "idle" => succ[p] = {}

\* The refinement property: every frontier the parallel algorithm has chosen is
\* always one of the successors the last committing process read.
Refines ==
    frontier # NoNode =>
        \E p \in Procs : pc[p] = "done" /\ frontier \in succ[p]

====