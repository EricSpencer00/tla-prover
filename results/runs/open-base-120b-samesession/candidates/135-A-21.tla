---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, ReachabilityAlg \* the sequential Misra reachability algorithm
\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANT Nodes
CONSTANT Root
CONSTANT Succ

\* Concrete instance for model checking
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root  = 1

\* Each node has exactly two successors, chosen deterministically
ASSUME Succ = [
    1 |-> {2,3},
    2 |-> {3,4},
    3 |-> {1,4},
    4 |-> {1,2}
]

\*--------------------------------------------------------------------
\* Operator that substitutes for the generic Succ used in the
\* algorithm specification
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll == Succ

\*--------------------------------------------------------------------
\* Limited version of Seq to keep the state space finite
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables (as defined in ReachabilityAlg)
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Initial state (instantiated with the concrete graph)
\*--------------------------------------------------------------------
Init ==
    /\ marked   = {Root}
    /\ frontier = {}
    /\ pc       = "start"

\*--------------------------------------------------------------------
\* Next-state relation (inherited from the algorithm; we give a
\* simple concrete version that respects the intended behaviour)
\*--------------------------------------------------------------------
Next ==
    \/ /\ pc = "start"
       /\ frontier' = ConnectedToSomeButNotAll[Root]
       /\ marked'   = marked
       /\ pc'       = "explore"
    \/ /\ pc = "explore"
       /\ \E n \in frontier :
            /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked)
            /\ marked'   = marked \cup {n}
            /\ pc'       = IF frontier' = {} THEN "done" ELSE "explore"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
vars == <<marked, frontier, pc>>
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "explore", "done"}

\*--------------------------------------------------------------------
\* Helper: reachability via bounded sequences
\*--------------------------------------------------------------------
Reachable(n) ==
    \E p \in LimitedSeq(Nodes) :
        /\ Len(p) > 0
        /\ p[1] = Root
        /\ p[Len(p)] = n
        /\ \A i \in 1..(Len(p)-1) : p[i+1] \in ConnectedToSomeButNotAll[p[i]]

\*--------------------------------------------------------------------
\* Invariant 1: successor closure
\*--------------------------------------------------------------------
Inv1 ==
    \A n \in marked :
        ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

\*--------------------------------------------------------------------
\* Invariant 2: frontier never overlaps marked
\*--------------------------------------------------------------------
Inv2 ==
    frontier \cap marked = {}

\*--------------------------------------------------------------------
\* Invariant 3: every reachable node is either marked or in frontier
\*--------------------------------------------------------------------
Inv3 ==
    \A n \in Nodes :
        Reachable(n) => n \in marked \cup frontier

\*--------------------------------------------------------------------
\* Partial correctness: when finished, marked equals the set of
\* reachable nodes.
\*--------------------------------------------------------------------
PartialCorrectness ==
    (pc = "done") => marked = { n \in Nodes : Reachable(n) }

\*--------------------------------------------------------------------
\* Liveness property: termination
\*--------------------------------------------------------------------
Termination == <> (pc = "done")

\*--------------------------------------------------------------------
\* List of invariants and properties for the model checker
\*--------------------------------------------------------------------
\* (the .cfg file will refer to these names)
\*--------------------------------------------------------------------
THEOREM TypeOKInv   == Spec => []TypeOK
THEOREM Inv1Inv     == Spec => []Inv1
THEOREM Inv2Inv     == Spec => []Inv2
THEOREM Inv3Inv     == Spec => []Inv3
THEOREM PartialCorr == Spec => []PartialCorrectness
THEOREM TermProp    == Spec => Termination

====