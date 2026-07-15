---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Node == Nodes

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The program counter distinguishes the two phases of the sequential
\* algorithm: "Init" (before the first iteration) and "Iter" (the loop body).
PC == {"Init", "Iter"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = "Init"
    /\ marked = {Root}
    /\ frontier = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* In the "Init" phase we populate the frontier with the successors of
\* the root node.  This mirrors the first step of the sequential
\* Misra algorithm.
InitStep ==
    /\ pc = "Init"
    /\ frontier = Succ[Root]
    /\ pc' = "Iter"
    /\ UNCHANGED marked

\* Main loop body: if the frontier is empty we have reached a fixed point,
\* otherwise we move one node from the frontier to the marked set and
\* add its successors.
Iter ==
    \/ /\ frontier = {}
       /\ UNCHANGED <<marked, frontier, pc>>
    \/ /\ frontier # {}
       /\ LET n == CHOOSE x \in frontier : TRUE IN
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup Succ[n]
          /\ pc' = "Iter"

\* The overall Next relation combines the two actions.
Next == InitStep \/ Iter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Type correctness: all variables contain only nodes and the pc is valid.
TypeOK ==
    /\ pc \in PC
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

\* Inv1: Successor closure – every node in the frontier is a successor of
\* a marked node.
Inv1 ==
    \A n \in frontier : \E m \in marked : n \in Succ[m]

\* Inv2: Reachability decomposition – the set of marked nodes together with
\* the frontier equals the set of nodes reachable from the root in at most
\* |Nodes| steps.
Reachable ==
    { n \in Nodes :
        \E s \in Seq :
          Len(s) = 1 + Len(s) /\ Len(s) <= Cardinality(Nodes) /\
          s[1] = Root /\ s[Len(s)] = n /\
          \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }
Inv2 ==
    marked \cup frontier = Reachable

\* Inv3: Reachable set equality – the algorithm eventually marks exactly the
\* reachable nodes.
Inv3 ==
    marked = Reachable

\* Partial correctness – when the algorithm stabilises (frontier empty) the
\* marked set equals the set of all nodes reachable from the root.
PartialCorrectness ==
    /\ frontier = {}
    => marked = Reachable

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
\* Termination: eventually the frontier becomes empty.
Termination == <> (frontier = {})

====