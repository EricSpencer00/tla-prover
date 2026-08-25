---- MODULE ReachableProofs ----
EXTENDS Naturals, SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* State vector
\* ----------------------------------------------------------------------
vars == << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
INIT ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "start"

\* ----------------------------------------------------------------------
\* Next-state relation (illustrative)
\* ----------------------------------------------------------------------
NEXT ==
    \/ /\ pc = "start"
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup { s \in Nodes : s \in Succ[n] }
            /\ pc'       = "start"
    \/ /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED << marked, frontier >>

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor property
\* ----------------------------------------------------------------------
Inv1 ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
         \A s \in Succ[n] :
            s \in marked \/ s \in frontier

\* ----------------------------------------------------------------------
\* Invariant 2: reachable-from equivalence (proved via Lemma 1)
\* ----------------------------------------------------------------------
Inv2 ==
    ReachableFrom(marked) \cup ReachableFrom(frontier) =
    ReachableFrom(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: marked set characterises reachability (proved via Lemma 2&3)
\* ----------------------------------------------------------------------
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

\* ----------------------------------------------------------------------
\* Partial‑correctness theorem (termination condition)
\* ----------------------------------------------------------------------
TerminationTheorem ==
    /\ frontier = {}
    /\ pc = "done"
    => marked = ReachableFrom({Root})

PROPERTIES == << TerminationTheorem >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == INIT /\ [][NEXT]_vars

====