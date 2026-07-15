---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* State variables inherited from the sequential Misra reachability algorithm
\* marked - set of nodes already proven reachable
\* frontier - set of nodes whose successors are yet to be examined
\* pc - program counter (captures which step of the algorithm we are in)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Node == Nodes
SeqNode == Seq

\* ----------------------------------------------------------------------
\* Initial state (inherits from the algorithm specification)
\* Initialization: only the root node is marked, frontier contains the root,
\* and program counter is set to the initial step "Init".
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "Init"

\* ----------------------------------------------------------------------
\* Next-state relation (inherits actions from the algorithm)
\* For simplicity we model the core loop of the reachability algorithm:
\*   - Choose a node n from frontier
\*   - Add its successors (according to the concrete graph Succ) to frontier
\*   - Move n from frontier to marked
\* The algorithm terminates when frontier becomes empty.
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Init"
       /\ pc' = "Loop"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Loop"
       /\ frontier # {}
       /\ \E n \in frontier:
            /\ let newFrontier == (frontier \ {n}) \cup Succ[n] in
               /\ marked' = marked \cup {n}
               /\ frontier' = newFrontier
               /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification formula required by the .cfg
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg
\* ----------------------------------------------------------------------
\* Type correctness: all variables have expected types
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Loop", "Done"}

\* Inv1: Successor closure – every node in frontier has all its successors
\*       (according to Succ) also in frontier ∪ marked.
Inv1 ==
    \A n \in frontier: Succ[n] \subseteq frontier \cup marked

\* Inv2: Reachability decomposition – marked, frontier, and the set of
\*       unreachable nodes partition Nodes.
Inv2 ==
    /\ marked \cap frontier = {}
    /\ marked \cup frontier \subseteq Nodes
    /\ Nodes \ (marked \cup frontier) = {}

\* Inv3: Reachable set equality – at termination, marked equals the set of
\*       nodes reachable from Root via paths respecting Succ.
ReachableFromRoot ==
    { m \in Nodes :
        \E s \in Seq :
            Len(s) > 0 /\ s[1] = Root /\ s[Len(s)] = m /\
            \A i \in 1..(Len(s)-1): s[i+1] \in Succ[s[i]] }

Inv3 ==
    pc = "Done" => marked = ReachableFromRoot

\* Partial correctness – when the algorithm is done, every node in marked
\* is indeed reachable from the root.
PartialCorrectness ==
    pc = "Done" => marked \subseteq ReachableFromRoot

\* ----------------------------------------------------------------------
\* Liveness property required by the .cfg
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Theorems (optional) to expose the invariants to TLC
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => []Termination

====