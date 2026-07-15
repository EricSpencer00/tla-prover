---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
\* The set of all directed edges of the graph (must be supplied by the
\* configuration file).  We keep it as an uninterpreted constant.
CONSTANT Edges

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Successors(n) == { m \in Nodes : <<n, m>> \in Edges }

\* Reachable nodes are defined recursively as the least fixpoint of
\* adding successors of already reached nodes.
\* This definition is standard in TLA+ for finite graphs.
Reachable == 
    LET R == [n \in Nodes |-> FALSE] IN
    (* Initially only the root is reachable *)
    LET Init == [n \in Nodes |-> IF n = Root THEN TRUE ELSE FALSE] IN
    (* Iteratively add successors until a fixpoint is reached *)
    LET Step(R) == 
        [n \in Nodes |-> 
            R[n] \/ \E m \in Nodes : R[m] /\ <<m, n>> \in Edges] 
    IN
    \E n \in Nat :
        LET Rn == [i \in Nat |-> IF i < n THEN Step(R) ELSE R][n] IN
        /\ \A i \in Nat : i >= n => Rn = Step(Rn)
        /\ Rn

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Type invariant (part of Invariant1)
\* ----------------------------------------------------------------------
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Visit", "Done"}

\* ----------------------------------------------------------------------
\* Initial state (Spec's Init)
\* ----------------------------------------------------------------------
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Visit"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Visit == 
    /\ pc = "Visit"
    /\ \E n \in frontier :
        /\ pc' = "Visit"
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \cup Successors(n)) \ {n}
    /\ UNCHANGED pc

Done == 
    /\ pc = "Visit"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next == Visit \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and every successor of a marked node
\* is either already marked or in the frontier.
Inv1 == 
    /\ TypeOK
    /\ \A n \in marked : Successors(n) \subseteq marked \cup frontier

\* Invariant 2: marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier)
\* ReachableFrom(S) is defined as the set of nodes reachable from any node in S.
ReachableFrom(S) == 
    \{ n \in Nodes : \E m \in S : n \in ReachableFromSingle(m) \}

ReachableFromSingle(start) == 
    LET R == [n \in Nodes |-> FALSE] IN
    LET InitR == [n \in Nodes |-> IF n = start THEN TRUE ELSE FALSE] IN
    LET Fix(R) == 
        [n \in Nodes |-> 
            R[n] \/ \E m \in Nodes : R[m] /\ <<m, n>> \in Edges] 
    IN
    \E n \in Nat :
        LET Rn == [i \in Nat |-> IF i < n THEN Fix(R) ELSE R][n] IN
        /\ \A i \in Nat : i >= n => Rn = Fix(Rn)
        /\ Rn

Inv2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3: Reachable(Root) = marked ∪ ReachableFrom(frontier)
Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* ----------------------------------------------------------------------
\* The set of all invariants required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == Inv1 /\ Inv2 /\ Inv3

\* ----------------------------------------------------------------------
\* The property that the specification satisfies the invariants
\* ----------------------------------------------------------------------
PROPERTIES == Spec => []INVARIANTS

====