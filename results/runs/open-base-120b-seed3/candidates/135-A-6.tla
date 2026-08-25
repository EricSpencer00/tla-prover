---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\*-------------------------------------------------
\* Concrete values for the constants (can be overridden
\* by the .cfg file). The model uses four nodes {0,1,2,3}
\* with a deterministic 2‑successor graph.
\*-------------------------------------------------
ASSUME Nodes = 0..3
ASSUME Root  = 0

\*-------------------------------------------------
\* Bounded version of the sequence operator.
\* The configuration replaces the standard Seq with this.
\*-------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*-------------------------------------------------
\* Finite graph where each node has exactly two successors.
\* The .cfg substitutes this operator for Succ.
\*-------------------------------------------------
ConnectedToSomeButNotAll ==
    [ n \in Nodes |-> { (n + 1) % 4 , (n + 2) % 4 } ]

\*-------------------------------------------------
\* State variables of the sequential reachability algorithm.
\*-------------------------------------------------
VARIABLES marked, frontier, pc

\*-------------------------------------------------
\* Initial state.
\*-------------------------------------------------
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Run"

\*-------------------------------------------------
\* Transition relation (single‑process version).
\*-------------------------------------------------
Next ==
    \/ /\ pc = "Run"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
            /\ pc'       = "Run"
    \/ /\ pc = "Run"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>

\*-------------------------------------------------
\* Full specification.
\*-------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*-------------------------------------------------
\* Type correctness invariant.
\*-------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

\*-------------------------------------------------
\* Invariant 1: successor closure.
\*-------------------------------------------------
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \/ Succ[n] \subseteq frontier

\*-------------------------------------------------
\* Invariant 2: frontier equals reachable nodes not yet marked.
\*-------------------------------------------------
Inv2 ==
    frontier = (Reachable(Root) \ marked)

\*-------------------------------------------------
\* Invariant 3: when finished, marked equals the reachable set.
\*-------------------------------------------------
Inv3 ==
    (pc = "Done") => marked = Reachable(Root)

\*-------------------------------------------------
\* Partial correctness property (identical to Inv3).
\*-------------------------------------------------
PartialCorrectness == Inv3

\*-------------------------------------------------
\* Reachable set defined via bounded paths.
\*-------------------------------------------------
Reachable(start) ==
    { n \in Nodes :
        \E s \in LimitedSeq(Nodes) :
            /\ Len(s) > 0
            /\ s[1] = start
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

\*-------------------------------------------------
\* Liveness property: the algorithm eventually terminates.
\*-------------------------------------------------
Termination == <> (pc = "Done")

====