---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,          \* The finite set of graph nodes (e.g., {1,2,3,4})
    Root,           \* The designated start node (must be in Nodes)
    Procs,          \* The finite set of worker processes (e.g., {1,2})
    Succ,           \* A function Nodes -> Seq(2) giving exactly two successors per node
    Seq             \* Upper bound on the length of any sequence (here = Cardinality(Nodes))

\* ----------------------------------------------------------------------
\* Derived constant: the set of all possible (ordered) pairs of distinct nodes
\* used for typing checks.
AllPairs == { <<i, j>> : i \in Nodes, j \in Nodes, i # j }

\* ----------------------------------------------------------------------
\* State variables (exactly the ones required by the parallel algorithm)
VARIABLES
    marked,         \* Set of nodes already explored (shared)
    frontier,       \* Set of nodes currently being processed (shared)
    pc,             \* Program counter per process: pc[p] ∈ {"Idle", "Select", "Process", "Done"}
    sel,            \* Selected node per process (or NULL when none)
    succSet         \* Successor set per process (subset of Nodes, derived from Succ)

\* ----------------------------------------------------------------------
\* Helper definitions
\* The constant Succ maps a node to a sequence of exactly two distinct successors.
SuccSet(n) == { Succ[n][i] : i \in 1..Length(Succ[n]) }

\* ----------------------------------------------------------------------
\* Initial state (matches the sequential configuration with bounded sequences)
Init ==
    /\ marked = {}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> "Idle"]
    /\ sel = [p \in Procs |-> NULL]
    /\ succSet = [p \in Procs |-> {}]
    /\ marked' = {}
    /\ frontier' = {Root}
    /\ pc' = [p \in Procs |-> "Select"]
    /\ sel' = [p \in Procs |-> NULL]
    /\ succSet' = [p \in Procs |-> {}]

\* ----------------------------------------------------------------------
\* Actions
Select(p) ==
    /\ pc[p] = "Select"
    /\ frontier # {}               \* there is at least one node to pick
    /\ LET n == CHOOSE m \in frontier : TRUE IN
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
       /\ succSet' = [succSet EXCEPT ![p] = SuccSet(n)]
    /\ pc' = [pc EXCEPT ![p] = "Process"]
    /\ UNCHANGED <<marked, pc, frontier, succSet, sel>>

Process(p) ==
    /\ pc[p] = "Process"
    /\ sel[p] # NULL
    /\ marked' = marked \cup {sel[p]}
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<frontier, sel, succSet, pc>>

UpdateFrontier ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ frontier' = frontier \cup \bigcup_{p \in Procs} succSet[p]
    /\ pc' = [p \in Procs |-> "Idle"]
    /\ sel' = [p \in Procs |-> NULL]
    /\ succSet' = [p \in Procs |-> {}]
    /\ UNCHANGED <<marked>>

Done ==
    /\ \A p \in Procs : pc[p] = "Idle"
    /\ frontier = {}
    /\ UNCHANGED <<marked, frontier, pc, sel, succSet>>

Next ==
    \/ \E p \in Procs : Select(p)
    \/ \E p \in Procs : Process(p)
    \/ UpdateFrontier
    \/ Done

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness + control-flow properties)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs :
          /\ pc[p] \in {"Idle", "Select", "Process", "Done"}
          /\ (pc[p] = "Select" => sel[p] = NULL)
          /\ (pc[p] = "Process" => sel[p] \in Nodes)
          /\ (pc[p] = "Done" => sel[p] = NULL)
    /\ \A p \in Procs : succSet[p] \subseteq Nodes
    /\ \A p \in Procs : pc[p] = "Select" => frontier # {}
    /\ \A p \in Procs : pc[p] = "Process" => sel[p] # NULL

\* ----------------------------------------------------------------------
\* Refinement property (stuttering-safe relation to the sequential Misra algorithm)
\* For illustration we state that every node eventually becomes marked
\* if reachable from Root, which is a safety consequence of the invariant.
Refines ==
    \A n \in Nodes :
        (n \in ReachableFromRoot) => n \in marked

\* Helper: the set of nodes reachable from the root using the Succ relation
ReachableFromRoot ==
    RECURSIVE Reach(_)
    Reach(x) ==
        IF x = Root THEN {Root}
        ELSE {x} \cup \bigcup_{s \in SuccSet(x)} Reach(s)

====