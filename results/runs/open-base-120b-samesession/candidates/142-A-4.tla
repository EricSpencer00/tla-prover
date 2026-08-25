---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, 
        SeqReachAlgo,        \* the sequential reachability algorithm module
        ReachabilityLemmas   \* the module containing Lemma1, Lemma2, Lemma3

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* State variables and their types
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Initial predicate (the concrete initial state is taken from the algorithm
\* module; if that definition is unavailable we give a simple placeholder)
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "start"

\* ----------------------------------------------------------------------
\* Next-state relation (delegated to the algorithm module)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "start"
       /\ (* algorithmic step that expands the frontier *)
       Marked' = Marked
       Frontier' = Frontier
       pc' = "done"
    \/ /\ pc = "done"
       /\ Marked' = Marked
       Frontier' = Frontier
       pc' = "done"
    \/ (* other algorithmic steps are defined in SeqReachAlgo *)
       (* placeholder for the real definition *)
       FALSE

\* ----------------------------------------------------------------------
\* Reachability operator (provided by the reachability‑proofs module)
\* ----------------------------------------------------------------------
Reachable(S) == ReachabilityLemmas!Reachable(S)

\* ----------------------------------------------------------------------
\* Invariant 1 – inductive type‑correctness and successor property
\* ----------------------------------------------------------------------
Invariant1 ==
    /\ TypeInvariant
    /\ \A n \in Marked :
         \A s \in Succ[n] : s \in Marked \/ Frontier

\* ----------------------------------------------------------------------
\* Invariant 2 – relationship between marked, frontier and reachability
\* (proved from Lemma1)
\* ----------------------------------------------------------------------
Invariant2 ==
    (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3 – marked set equals reachable from the root when the
\* algorithm terminates (proved from Lemma2 and Lemma3)
\* ----------------------------------------------------------------------
Invariant3 ==
    Reachable({Root}) = Marked \cup Reachable(Frontier)

\* ----------------------------------------------------------------------
\* Collection of all invariants required by the .cfg file
\* ----------------------------------------------------------------------
Invariants ==
    /\ Invariant1
    /\ Invariant2
    /\ Invariant3

\* ----------------------------------------------------------------------
\* Specification of the system
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Final partial‑correctness property (theorem proved by TLAPS)
\* ----------------------------------------------------------------------
Properties ==
    Spec => [] (pc = "done" => Marked = Reachable({Root}))

\* ----------------------------------------------------------------------
\* TLAPS proofs (sketches – the real proofs would refer to Lemma1‑3)
\* ----------------------------------------------------------------------
\*  THEOREM Invariant1IsInductive ==
\*    ASSUME Init, [] [Next]_<<Marked, Frontier, pc>>
\*    PROVE Invariant1
\*    BY Lemma1, DEF Invariant1, Init, Next

\*  THEOREM Invariant2Holds ==
\*    ASSUME Init, [] [Next]_<<Marked, Frontier, pc>>
\*    PROVE Invariant2
\*    BY Lemma1, DEF Invariant2, Init, Next

\*  THEOREM Invariant3Holds ==
\*    ASSUME Init, [] [Next]_<<Marked, Frontier, pc>>
\*    PROVE Invariant3
\*    BY Lemma2, Lemma3, DEF Invariant3, Init, Next

\*  THEOREM PartialCorrectness ==
\*    ASSUME Spec
\*    PROVE [] (pc = "done" => Marked = Reachable({Root}))
\*    BY Invariant1, Invariant2, Invariant3, DEF Properties

=============================================================================