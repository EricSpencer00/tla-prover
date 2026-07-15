---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* Derived sets and functions
\* ----------------------------------------------------------------------
Node == Nodes

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
NodeSeq == [i \in 1..Cardinality(Nodes) |-> Node]

\* ----------------------------------------------------------------------
\* Initial state (inherited from the algorithm, instantiated with the
\* concrete graph and bounded sequences)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"
    /\ UNCHANGED <<Seq>>

\* ----------------------------------------------------------------------
\* Actions (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
AddFrontier ==
    /\ pc = "Init"
    /\ frontier # {}
    /\ frontier' = {}
    /\ marked' = marked \cup frontier
    /\ pc' = "Step"
    /\ UNCHANGED Seq

Step ==
    /\ pc = "Step"
    /\ \E n \in frontier :
        LET succSet == { Succ[n][j] : j \in 1..2 } IN
        /\ frontier' = succSet \ marked
        /\ marked' = marked
        /\ pc' = IF frontier' = {} THEN "Done" ELSE "Step"
    /\ UNCHANGED Seq

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc, Seq>>

Next ==
    \/ AddFrontier
    \/ Step
    \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, Seq>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Step", "Done"}
    /\ Seq \in Seq(NodeSeq)

\* ----------------------------------------------------------------------
\* Algorithm invariants
\* ----------------------------------------------------------------------
Inv1 == \A n \in marked : n \in NodeSeq

Inv2 == \A n \in marked : n = Root \/ \E m \in marked : n \in { Succ[m][j] : j \in 1..2 }

Inv3 == marked = { n \in Nodes : \E seq \in Seq :
                 /\ Len(seq) > 0
                 /\ seq[1] = Root
                 /\ seq[Len(seq)] = n
                 /\ \A k \in 1..(Len(seq)-1) : seq[k+1] \in { Succ[seq[k]][j] : j \in 1..2 } }

PartialCorrectness == \A n \in Nodes :
    (n \in marked) \equiv
    (\E seq \in Seq :
        /\ Len(seq) > 0
        /\ seq[1] = Root
        /\ seq[Len(seq)] = n
        /\ \A k \in 1..(Len(seq)-1) : seq[k+1] \in { Succ[seq[k]][j] : j \in 1..2 })

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

====