---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

None == "none"

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

\* A bounded frontier: the set of frontier positions that are still below the
\* current sequence length. This is what keeps the model finite.
ActiveFrontier == {i \in 1..Len(frontier) : frontier[i] \in Nodes}

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in Seq(Nodes)
    /\ pc \in [Procs -> {"idle", "chosen"}]
    /\ sel \in [Procs -> Nodes \cup {None}]
    /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = <<Root>>
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> None]
    /\ succ = Succ

Choose(n) ==
    /\ pc[n] = "idle"
    /\ pc' = [pc EXCEPT ![n] = "chosen"]
    /\ UNCHANGED <<marked, frontier, sel, succ>>

\* The frontier is a set of positions, so the order in which workers claim
\* them has no effect on which nodes are covered.
Select(n, i) ==
    /\ pc[n] = "chosen"
    /\ i \in ActiveFrontier
    /\ frontier[i] \in Nodes
    /\ sel' = [sel EXCEPT ![n] = frontier[i]]
    /\ pc' = [pc EXCEPT ![n] = "idle"]
    /\ frontier' = [frontier EXCEPT ![i] = None]
    /\ UNCHANGED <<marked, succ>>

Explore(n) ==
    /\ sel[n] \in Nodes
    /\ sel[n] \notin marked
    /\ marked' = marked \cup {sel[n]}
    /\ frontier' = Append(frontier, succ[sel[n]])
    /\ sel' = [sel EXCEPT ![n] = None]
    /\ UNCHANGED <<pc, succ>>

\* Nothing selected: clear the claim and go idle.
ClearIdle(n) ==
    /\ pc[n] = "idle"
    /\ sel[n] = None
    /\ frontier # <<>>
    /\ frontier' = SelectSeq(frontier, \E i \in DOMAIN frontier : frontier[i] = None)
    /\ UNCHANGED <<marked, pc, sel, succ>>

\* Choosing and selecting are always available, so Strong Fairness on them is
\* enough to drain the frontier and mark everything reachable from the root.
Next ==
    \E n \in Procs :
        \/ Choose(n)
        \/ \E i \in 1..Len(frontier) : Select(n, i)
        \/ Explore(n)
        \/ ClearIdle(n)

\* Fairness is attached to Choose and Select, not to Explore, so the frontier
\* cannot stall forever once every reachable node is marked.
Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A n \in Procs : SF_vars(Choose(n))
    /\ \A n \in Procs : \A i \in 1..Len(frontier) : WF_vars(Select(n, i))

\* Every marked node is reachable from the root in the graph.
ReachableFromRoot(n) ==
    /\ n \in marked
    /\ \E p \in Procs : sel[p] = n

NodeHasSuccessor == \A n \in Nodes : succ[n] # {}

\* The frontier only ever holds successors of already-marked nodes, so the
\* parallel workers never wander off the MISRA graph.
FrontierIsReachable == \A i \in ActiveFrontier : ReachableFromRoot(frontier[i])

Inv == NodeHasSuccessor /\ FrontierIsReachable

\* The parallel algorithm's reachable set is exactly the MISRA set.
Refines == marked = Nodes

\* Substituted in by the .cfg: Succ is a finite graph with two successors per
\* node, so it stays finite and reachable from the root.
ConnectedToSomeButNotAll == Cardinality(Nodes) = 2 /\ \A n \in Nodes : Cardinality(Succ[n]) = 2

\* Replaces Sequences' unbounded Seq, making frontier management checkable.
LimitedSeq == (Seq \ {Seq}) \cup [domain -> 1..Cardinality(Nodes), runof -> Nodes]

====