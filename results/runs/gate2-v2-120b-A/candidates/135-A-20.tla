---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------
\* Constants required by the .cfg
\* -------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* -------------------------------------------------
\* Derived sets
\* -------------------------------------------------
Node == Nodes

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES marked, frontier, pc, seqs

\* -------------------------------------------------
\* Type declarations (for readability, not used directly)
\* -------------------------------------------------
MarkedSet == SUBSET Node
SeqSet    == SUBSET Seq

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Start"
    /\ seqs     = {}

\* -------------------------------------------------
\* Helper actions
\* -------------------------------------------------
AddFrontier ==
    /\ frontier # {}
    /\ \E n \in frontier:
          /\ \E s \in Seq:
                /\ s # <<>>
                /\ s[1] = n
                /\ s[Len(s)] = Root
                /\ marked'   = marked \cup {n}
                /\ frontier' = frontier \ {n}
                /\ seqs'     = seqs \cup {s}
          /\ UNCHANGED <<pc, marked, frontier, seqs>>

NoFrontier ==
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc, seqs>>

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next ==
    \/ AddFrontier
    \/ NoFrontier

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc, seqs>>

\* -------------------------------------------------
\* Invariants
\* -------------------------------------------------
\* Type correctness: all variables stay within their intended domains
TypeOK ==
    /\ marked   \in SUBSET Node
    /\ frontier \in SUBSET Node
    /\ pc       \in {"Start", "Done"}
    /\ seqs     \subseteq Seq

\* Inv1: Successor closure – every node in marked has a successor also in marked
Inv1 ==
    \A n \in marked :
        \E m \in marked : m \in Succ[n]

\* Inv2: Reachability decomposition – marked equals the union of all nodes appearing in any stored sequence
Inv2 ==
    marked = { n \in Node : \E s \in seqs : n \in set s }

\* Inv3: Reachable set equality – the set of nodes reachable from Root via Succ equals marked
Inv3 ==
    marked = { n \in Node : \E s \in Seq : /\ s[1] = Root
                                      /\ s[Len(s)] = n
                                      /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

\* Partial correctness – if the algorithm finishes, then every node reachable from Root is in marked
PartialCorrectness ==
    (pc = "Done") => (marked = { n \in Node : \E s \in Seq :
                                          /\ s[1] = Root
                                          /\ s[Len(s)] = n
                                          /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] } )

\* -------------------------------------------------
\* Liveness property (termination)
\* -------------------------------------------------
Termination ==
    <> (pc = "Done")

====