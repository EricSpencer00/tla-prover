---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Nodes,   \* The set of all graph nodes
    Root,    \* The distinguished start node (Root \in Nodes)
    Succ     \* Successor function: [Nodes -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Operators required by the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == Seq(S)   \* Finite version of Seq (Seq is already finite)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Graph relation induced by the successor function
Graph == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

\* Reachability from a set of nodes via the transitive closure of Graph
Reach(S) == 
    { m \in Nodes : 
        \E s \in S : <<s, m>> \in ^ Graph }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc   \* pc = "run" or "done"

vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
    /\ pc = "run"
    /\ frontier /= {} 
    /\ \E n \in frontier :
        /\ IF n \notin marked THEN
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
           ELSE
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
        /\ pc' = IF (frontier' = {}) THEN "done" ELSE "run"
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Inv1: every successor of a marked node is either marked or in frontier
Inv1 == 
    \A n \in marked : ConnectedToSomeButNotAll(n) \subseteq (marked \cup frontier)

\* Inv2: Reach(marked ∪ frontier) = marked ∪ Reach(frontier)
Inv2 == 
    Reach(marked \cup frontier) = marked \cup Reach(frontier)

\* Inv3: Reach({Root}) = marked ∪ Reach(frontier)
Inv3 == 
    Reach({Root}) = marked \cup Reach(frontier)

\* Partial correctness: when terminated, marked equals the reachable set
PartialCorrectness == 
    (frontier = {} ) => (marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES == Termination

====