---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\* Concrete values for the constants (can be overridden by the .cfg file)
ASSUME Nodes = 1..4
ASSUME Root  = 1
ASSUME Succ  = ConnectedToSomeButNotAll

\* ----------------------------------------------------------------------
\* Finite successor relation: each node has exactly two successors
\* The .cfg substitutes Succ with ConnectedToSomeButNotAll, therefore we
\* define the operator with that exact name.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll ==
    [n \in Nodes |-> 
        IF n = 1 THEN {2, 3}
        ELSE IF n = 2 THEN {1, 4}
        ELSE IF n = 3 THEN {1, 4}
        ELSE {2, 3}
    ]

\* ----------------------------------------------------------------------
\* LimitedSeq: a finite version of the generic Seq operator
\* The .cfg replaces Seq with LimitedSeq, so we keep the original Seq
\* from Sequences unchanged.
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Variables of the sequential Misra reachability algorithm
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Initial state: only the root is marked and in the frontier
\* ----------------------------------------------------------------------
Init ==
    /\ Marked   = {Root}
    /\ Frontier = {Root}
    /\ pc       = "run"

\* ----------------------------------------------------------------------
\* One step of the algorithm:
\*   - pick an element n from the frontier,
\*   - add its successors to the frontier (if not already marked),
\*   - move n to the marked set,
\*   - when the frontier becomes empty, go to the done state.
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "run"
       /\ Frontier # {}
       /\ \E n \in Frontier :
            /\ Marked'   = Marked \cup {n}
            /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ Marked)
            /\ pc'       = "run"
    \/ /\ pc = "run"
       /\ Frontier = {}
       /\ pc'       = "done"
       /\ UNCHANGED <<Marked, Frontier>>

\* ----------------------------------------------------------------------
\* Specification of the system
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Marked   \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Reachable set defined via bounded paths (LimitedSeq)
\* ----------------------------------------------------------------------
Reachable ==
    { n \in Nodes :
        \E s \in LimitedSeq(Nodes) :
            /\ Len(s) > 0
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..Len(s)-1 :
                 s[i+1] \in ConnectedToSomeButNotAll[s[i]]
    }

\* ----------------------------------------------------------------------
\* Invariant 1: successors of any marked node are either already marked
\*            or are in the frontier (closure property during execution)
\* ----------------------------------------------------------------------
Inv1 ==
    \A n \in Marked :
        ConnectedToSomeButNotAll[n] \subseteq (Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 2: every marked node is reachable from the root
\* ----------------------------------------------------------------------
Inv2 == Marked \subseteq Reachable

\* ----------------------------------------------------------------------
\* Invariant 3: the frontier consists exactly of reachable nodes that are
\*            not yet marked
\* ----------------------------------------------------------------------
Inv3 == Frontier = Reachable \ Marked

\* ----------------------------------------------------------------------
\* Partial correctness: when the algorithm terminates, all reachable
\* nodes are marked and the frontier is empty
\* ----------------------------------------------------------------------
PartialCorrectness ==
    pc = "done" => /\ Frontier = {}
                 /\ Marked   = Reachable

\* ----------------------------------------------------------------------
\* Liveness property: the algorithm eventually reaches the done state
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

\* ----------------------------------------------------------------------
\* List of invariants for the TLC configuration
\* ----------------------------------------------------------------------
THEOREM TypeOKInvariant == Spec => []TypeOK
THEOREM Inv1Invariant   == Spec => []Inv1
THEOREM Inv2Invariant   == Spec => []Inv2
THEOREM Inv3Invariant   == Spec => []Inv3
THEOREM PCInvariant     == Spec => []PartialCorrectness

====