---- MODULE ReachableProofs ----
EXTENDS SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\*  State variable definitions (inherited from the algorithm module)
\* ----------------------------------------------------------------------
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

Next == 
    \* The actual step relation is taken from the sequential reachability
    \* algorithm module (SeqReachAlg).  We simply alias it here.
    SeqNext

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\*  Helper definitions (provided by the extended modules)
\*   - Succ[n]  : the set of successors of node n
\*   - Reach(S) : the set of nodes reachable from a set S
\*   - Lemma1, Lemma2, Lemma3 : graph‑theoretic lemmas used in proofs
\* ----------------------------------------------------------------------
\* (These are assumed to be defined in the modules that we extend.)

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
Invariant1 == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked : \A s \in Succ[n] : s \in marked \/ s \in frontier

Invariant2 == 
    /\ marked \cup Reach(frontier) = Reach(marked \cup frontier)
    \* Direct consequence of Lemma1

Invariant3 == 
    /\ Reach({Root}) = marked \cup Reach(frontier)
    \* Follows from Lemma2 and Lemma3

INVARIANTS == {Invariant1, Invariant2, Invariant3}

\* ----------------------------------------------------------------------
\*  Partial‑correctness property (termination is identified by pc = "done")
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "done") => marked = Reach({Root})

PROPERTIES == {PartialCorrectness}
====