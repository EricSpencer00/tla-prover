---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------------------------------
\* Constants supplied by the configuration
\* -------------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\* -------------------------------------------------------------------------
\* Operator substituted for Succ by the .cfg file
\* -------------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* -------------------------------------------------------------------------
\* A finite version of Seq for model checking (replaces Seq via LimitedSeq)
\* -------------------------------------------------------------------------
MaxSeqLen == 5
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* -------------------------------------------------------------------------
\* State variables
\* -------------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* -------------------------------------------------------------------------
\* Reachability definitions
\* -------------------------------------------------------------------------
R == [n \in Nodes, m \in Nodes |-> m \in Succ[n]]

ReachFrom(n) == { m \in Nodes : <<n, m>> \in TC(R) } \cup {n}

ReachFromSet(S) == UNION { ReachFrom(n) : n \in S }

ReachAll == ReachFrom(Root)

\* -------------------------------------------------------------------------
\* Initial state
\* -------------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* -------------------------------------------------------------------------
\* Next-state relation (the main action)
\* -------------------------------------------------------------------------
Next ==
    \/ /\ pc = "Run"
       /\ frontier # {}
       /\ \E n \in frontier :
            \/ /\ n \notin marked
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
               /\ pc' = "Run"
            \/ /\ n \in marked
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
               /\ pc' = "Run"
    \/ /\ pc = "Run"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* -------------------------------------------------------------------------
\* Specification
\* -------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* -------------------------------------------------------------------------
\* Invariants
\* -------------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup ReachFromSet(frontier) = ReachFromSet(marked \cup frontier)

Inv3 ==
    ReachAll = marked \cup ReachFromSet(frontier)

PartialCorrectness ==
    /\ pc = "Done"
    /\ frontier = {}
    => marked = ReachAll

\* -------------------------------------------------------------------------
\* Liveness property (termination)
\* -------------------------------------------------------------------------
Termination == []<>(frontier = {})

\* -------------------------------------------------------------------------
\* Optional theorems for TLC (not required but harmless)
\* -------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
PROPERTY Termination

====