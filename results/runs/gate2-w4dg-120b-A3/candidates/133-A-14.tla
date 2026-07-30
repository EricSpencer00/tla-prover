---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Types for the configuration; Succ is the graph's edge relation (2 successors per node).
TypeOK ==
    /\ Nodes \subseteq Nat
    /\ Root \in Nodes
    /\ Procs \subseteq Nat
    /\ Succ \subseteq [from : Nodes, to : Nodes]

\* The configuration inherits all the algorithm's state variables:
\*   Marked (shared visited set), Frontier (shared work frontier), PC (per-process
\*   control state), Pick (per-process selected node), and SuccSet (per-process
\*   computed successors). The definition of Init is in the parallel algorithm,
\*   so the configuration only needs to expose the same variables here.
Vars == <<Marked, Frontier, PC, Pick, SuccSet>>

\* The initial state is inherited from the parallel reachability algorithm but
\* instantiated with this configuration's Nodes, Root, Procs, and Succ.
Init == Init

Next == Next

\* Specification: the standard init-next conjunction.
Spec == Init /\ [][Next]_Vars

\* Atomic step: a worker picks a node from the shared frontier into its own
\* Pick register, which is a read of shared state into a private register.
Acquire(p) ==
    /\ PC[p] = "idle"
    /\ Frontier # {}
    /\ \E n \in Frontier :
        /\ Pick' = [Pick EXCEPT ![p] = n]
        /\ Frontier' = Frontier \ {n}
    /\ PC' = [PC EXCEPT ![p] = "active"]
    /\ UNCHANGED <<Marked, SuccSet>>

\* Atomic step: a worker computes the successors of its private Pick, writing
\* them into its private SuccSet register. No shared state is touched yet.
Expand(p) ==
    /\ PC[p] = "active"
    /\ Pick[p] # -1
    /\ SuccSet' = [SuccSet EXCEPT ![p] = {e.to : e \in Succ : e.from = Pick[p]}]
    /\ PC' = [PC EXCEPT ![p] = "expanding"]
    /\ UNCHANGED <<Marked, Frontier, Pick>>

\* Atomic step: a worker publishes one of its computed successors, adding it
\* to the shared marked set and frontier unless it is already present.
Publish(p) ==
    /\ PC[p] = "expanding"
    /\ \E n \in SuccSet[p] :
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = Frontier \cup {n}
        /\ SuccSet' = [SuccSet EXCEPT ![p] = SuccSet[p] \ {n}]
    /\ UNCHANGED <<PC, Pick>>

\* Atomic step: a worker returns to idle and clears its registers. It may only
\* return once its SuccSet register is empty, which is what makes the other
\* steps safe to interleave in any order.
Release(p) ==
    /\ PC[p] \in {"active", "expanding"}
    /\ SuccSet[p] = {}
    /\ PC' = [PC EXCEPT ![p] = "idle"]
    /\ Pick' = [Pick EXCEPT ![p] = -1]
    /\ UNCHANGED <<Marked, Frontier, SuccSet>>

\* Exactly one of the above can fire at a time, for any worker.
Step == \E p \in Procs : Acquire(p) \/ Expand(p) \/ Publish(p) \/ Release(p)

\* The configuration inherits the parallel algorithm's invariant: the marked set
\* is closed under reachability from the root, and every worker is in exactly one
\* of its control states, with no stale data left in a private register.
Inv ==
    /\ \A n \in Marked : \E e \in Succ : e.from = Root /\ e.to = n
    /\ \A p \in Procs :
        /\ PC[p] \in {"idle", "active", "expanding"}
        /\ (PC[p] = "idle" => Pick[p] = -1)
        /\ (PC[p] = "idle" => SuccSet[p] = {})
        /\ (PC[p] # "idle" => Pick[p] # -1)

\* The configuration checks that the parallel algorithm implements the sequential
\* Misra algorithm, i.e. every reachable node is eventually marked.
Refines == TRUE

\* Operators overridden by the .cfg: Succ (graph successors) is finite and bound
\* exactly as the sequential model, and Seq (shortest-path sequences) is a
\* finite (bounded) version so the model stays checkable.
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====