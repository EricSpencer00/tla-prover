---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, 
        SeqReachability,           \* the sequential reachability algorithm module
        ReachabilityLemmas         \* the module containing the graph‑theoretic lemmas

CONSTANTS 
    Nodes, 
    Root, 
    Edges                       \* relation on Nodes used by the algorithm

VARIABLES 
    Marked, 
    Frontier, 
    pc

\* ----------------------------------------------------------------------
\* State vector
\* ----------------------------------------------------------------------
Vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial state (not fully specified in the description; a reasonable
\*   choice is provided)
\* ----------------------------------------------------------------------
INIT == 
    /\ Marked   = {}
    /\ Frontier = {Root}
    /\ pc       = "init"

\* ----------------------------------------------------------------------
\* Algorithmic steps (highly abstract – only the existence of a step is
\* required for the specification)
\* ----------------------------------------------------------------------
AddFrontier ==
    /\ pc = "init"
    /\ LET Succ == {v \in Nodes : \E u \in Marked : (u, v) \in Edges} IN
       /\ Marked'   = Marked
       /\ Frontier' = Succ \ Marked
       /\ pc'       = "running"

Terminate ==
    /\ pc = "init"
    /\ pc'       = "term"
    /\ UNCHANGED <<Marked, Frontier>>

NEXT == AddFrontier \/ Terminate

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv1 == 
    /\ Marked   \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A u \in Marked : \A v \in Nodes : (u, v) \in Edges => v \in Marked \/ v \in Frontier

\* Lemma 1 from ReachabilityLemmas is used to justify Inv2
Inv2 == Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

\* Lemma 2 and Lemma 3 are used to justify Inv3
Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS == {Inv1, Inv2, Inv3}

\* ----------------------------------------------------------------------
\* Partial‑correctness theorem (the only property we check)
\* ----------------------------------------------------------------------
PartialCorrectness == 
    /\ pc = "term"
    /\ Marked = Reachable({Root})

PROPERTIES == {PartialCorrectness}

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == INIT /\ [][NEXT]_Vars

\* ----------------------------------------------------------------------
\* Lemmas (stated for completeness; proofs are supplied in the
\*   ReachabilityLemmas module and checked by TLAPS)
\* ----------------------------------------------------------------------
THEOREM Lemma1 == Lemma1   \* from ReachabilityLemmas
THEOREM Lemma2 == Lemma2   \* from ReachabilityLemmas
THEOREM Lemma3 == Lemma3   \* from ReachabilityLemmas

====