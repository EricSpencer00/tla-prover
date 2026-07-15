---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

\*********************************************************************
\*  Constants required by the reference configuration
\*********************************************************************
CONSTANTS
    Nodes,   \* The set of node identifiers
    Root,    \* The distinguished start node
    Succ,    \* Function from a node to the set of its two successors
    Seq      \* Upper bound on the length of path sequences (override)

\*********************************************************************
\*  State variables (inherited from the sequential reachability algorithm)
\*********************************************************************
VARIABLES
    marked,   \* Set of nodes that have been discovered as reachable
    frontier, \* Set of nodes whose successors still need to be explored
    pc        \* Control variable: "Init", "Step", or "Done"

\*********************************************************************
\*  Helper definitions
\*********************************************************************
NodeSet == Nodes

\* The set of all possible finite sequences over NodeSet whose length
\* is bounded by the constant Seq (the model configuration sets Seq = 4).
BoundedSeq == { s \in Seq(Seq) : Len(s) <= Seq }

\*********************************************************************
\*  Initial state (inherited, instantiated with concrete graph)
\*********************************************************************
Init ==
    /\ marked   = {Root}
    /\ frontier = Succ[Root]
    /\ pc       = "Step"

\*********************************************************************
\*  Actions (inherited from the sequential algorithm)
\*********************************************************************
Step ==
    /\ pc = "Step"
    /\ \E n \in frontier :
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \cup Succ[n]) \ SetMinus marked'
    /\ pc' = IF frontier' = {} THEN "Done" ELSE "Step"

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

\*********************************************************************
\*  Next-state relation
\*********************************************************************
Next == Step \/ Done

\*********************************************************************
\*  Specification
\*********************************************************************
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*********************************************************************
\*  Invariants required by the configuration
\*********************************************************************
\* Type correctness: variables stay within their intended domains
TypeOK ==
    /\ marked   \in SUBSET NodeSet
    /\ frontier \in SUBSET NodeSet
    /\ pc       \in {"Init", "Step", "Done"}

\* Inv1: successor closure – every node in frontier is a successor of some marked node
Inv1 ==
    frontier \subseteq UNION { Succ[m] : m \in marked }

\* Inv2: reachability decomposition – marked is exactly those nodes reachable via a bounded path
Inv2 ==
    marked = { n \in NodeSet :
                \E s \in BoundedSeq :
                    /\ Len(s) >= 1
                    /\ s[1] = Root
                    /\ s[Len(s)] = n
                    /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

\* Inv3: reachable set equality – the set of nodes reachable by any (unbounded) path
\*          equals the set of nodes reachable by a bounded path (since the graph is finite,
\*          the bound Seq is sufficient)
Inv3 ==
    marked = { n \in NodeSet :
                \E s \in Seq(NodeSet) :
                    /\ Len(s) >= 1
                    /\ s[1] = Root
                    /\ s[Len(s)] = n
                    /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

\* Partial correctness – every node that is reachable in the graph is eventually marked
PartialCorrectness ==
    \A n \in NodeSet :
        ( \E s \in Seq(NodeSet) :
            /\ Len(s) >= 1
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] )
        => n \in marked

\*********************************************************************
\*  Liveness property (termination)
\*********************************************************************
Termination ==
    <> (pc = "Done")

\*********************************************************************
\*  Theorems (optional, just expose the names)
\*********************************************************************
THEOREM InitSpec == Init
THEOREM NextSpec == Next

=============================================================================