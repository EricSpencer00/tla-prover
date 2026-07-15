---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,   \* The finite set of all graph nodes
    Root,    \* The distinguished start node, assumed to be in Nodes
    Succ,    \* A function mapping each node to the set of its successors
    Seq      \* A constant used only for typing; its concrete value is irrelevant

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ReachableFrom(s) == 
    LET Recur(S) == 
        IF S = {} THEN {} 
        ELSE LET n == CHOOSE x \in S : TRUE IN 
             {n} \cup Recur(S \ {n} \cup Succ[n])
    IN Recur({s})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Terminated"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Running"
       /\ frontier # {}               \* there is at least one node to pick
       /\ \E n \in frontier :
            IF n \notin marked
            THEN /\ marked' = marked \cup {n}
                 /\ frontier' = frontier \cup Succ[n]
            ELSE /\ marked' = marked
                 /\ frontier' = frontier \ {n}
       /\ pc' = "Running"
    \/ /\ pc = "Running"
       /\ frontier = {}
       /\ marked' = marked
       /\ frontier' = frontier
       /\ pc' = "Terminated"
    \/ /\ pc = "Terminated"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* 1. Every successor of a marked node is in marked or frontier
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* 2. (Utility invariant) Not used directly in the safety theorem but kept for completeness
Inv2 == \A n \in frontier : n \notin marked

\* 3. Reachability invariant: all reachable nodes are either marked or reachable from the frontier
Inv3 == ReachableFrom(Root) = marked \cup ReachableFromSet(frontier)

ReachableFromSet(F) == 
    LET Recur(S) == 
        IF S = {} THEN {} 
        ELSE LET n == CHOOSE x \in S : TRUE IN 
             {n} \cup Recur(S \ {n} \cup Succ[n])
    IN Recur(F)

\* Partial correctness: when terminated, marked equals the reachable set
PartialCorrectness == 
    /\ pc = "Terminated"
    /\ marked = ReachableFrom(Root)

\* ----------------------------------------------------------------------
\* Liveness (property)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Terminated")

\* ----------------------------------------------------------------------
\* Theorem (optional, not required by the cfg but useful for sanity)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====