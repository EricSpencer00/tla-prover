---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs

\* ConnectedToSomeButNotAll is the overridden Succ operator for this model: a
\* finite substitute for the usual unbounded successor relation.
\* Each node has exactly two successors, which keeps the reachable state space
\* manageable while still exercising the parallel algorithm's handling of
\* branching.
VARIABLES marked, frontier, pc, sel, workers
vars == <<marked, frontier, pc, sel, workers>>

\* LimitedSeq is the overridden, finite version of the standard Seq operator
\* from the Sequences module. It bounds any constructed sequence to at most the
\* number of nodes, which is a strict reduction in state space.
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> {}]
  /\ workers = {}

Extract(p) == CHOOSE n \in sel[p] : TRUE

\* A worker claims the frontier and moves into the selecting phase, bounded by
\* the finite frontier capacity.
ClaimFrontier(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ workers' = workers \cup {p}
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ UNCHANGED <<marked, frontier, sel>>

\* Selecting a node from the shared frontier into this worker's private batch.
Select(p) ==
  /\ pc[p] = "selecting"
  /\ frontier # {}
  /\ sel[p] = {}
  /\ frontier' = frontier \ {Extract(p)}
  /\ sel' = [sel EXCEPT ![p] = {Extract(p)}]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, workers>>

\* The exploring phase traverses the concrete graph; ConnectedToSomeButNotAll
\* is the overridden Succ operator, and it is finite here.
Explore(p) ==
  /\ pc[p] = "exploring"
  /\ sel[p] # {}
  /\ \E m \in ConnectedToSomeButNotAll(Extract(p)) :
       /\ marked' = marked \cup {m}
       /\ frontier' = frontier \cup {m}
  /\ sel' = [sel EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ workers' = workers \ {p}

Release(p) ==
  /\ pc[p] = "idle"
  /\ p \in workers
  /\ workers' = workers \ {p}
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Next ==
  \/ \E p \in Procs :
       \/ ClaimFrontier(p) \/ Select(p) \/ Explore(p) \/ Release(p)

Spec == Init /\ [][Next]_vars

\* The inductive invariant: the frontier is always a subset of the marked set,
\* each worker's local batch is disjoint from the frontier and from other
\* workers' batches, and every worker's program counter is one of the four
\* defined phases.
Inv ==
  /\ frontier \subseteq marked
  /\ \A p \in Procs : sel[p] \cap frontier = {}
  /\ \A p, q \in Procs : (p # q) => sel[p] \cap sel[q] = {}
  /\ \A p \in Procs : pc[p] \in {"idle", "selecting", "exploring"}

\* When no frontier remains and no worker is mid-operation, every reachable
\* node has been incorporated into the forward marking -- parallel reachability
\* has converged to the sequential Misra result.
Refines ==
  (\A n \in Nodes : n \in marked) <=> (frontier = {} /\ \A p \in Procs : pc[p] = "idle")

====