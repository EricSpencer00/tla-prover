---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC, SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

\* State variables of the sequential reachability algorithm
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Definition of the set of variables for the temporal operators
\* ----------------------------------------------------------------------
vars == << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\* Initial state (as used in the original algorithm)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Actions of the algorithm (abstracted)
\* ----------------------------------------------------------------------
AddSuccessors ==
    /\ pc = "Run"
    /\ \E n \in marked :
          \E s \in Succ[n] :
              /\ s \notin marked
              /\ s \notin frontier
              /\ frontier' = frontier \cup {s}
              /\ UNCHANGED << marked, pc >>
NextFrontier ==
    /\ pc = "Run"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ UNCHANGED pc
Terminate ==
    /\ pc = "Run"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED << marked, frontier >>
Other ==
    /\ pc = "Done"
    /\ UNCHANGED << marked, frontier, pc >>

Next ==
    \/ AddSuccessors
    \/ NextFrontier
    \/ Terminate
    \/ Other

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor condition
\* ----------------------------------------------------------------------
TypeCorrectness ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

SuccCondition ==
    \A n \in marked :
        \A s \in Succ[n] :
            s \in marked \/ s \in frontier

Invariant1 == TypeCorrectness /\ SuccCondition

\* ----------------------------------------------------------------------
\* Invariant 2: relationship between marked, frontier and reachability
\* ----------------------------------------------------------------------
Invariant2 == 
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: marked set equals reachable set from the root (modulo frontier)
\* ----------------------------------------------------------------------
Invariant3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* ----------------------------------------------------------------------
\* Set of invariants required by the configuration
\* ----------------------------------------------------------------------
INVARIANTS == { Invariant1, Invariant2, Invariant3 }

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Final correctness property (partial correctness)
\* ----------------------------------------------------------------------
TerminationCorrectness ==
    [] (pc = "Done" => marked = ReachableFrom({Root}))

PROPERTIES == { TerminationCorrectness }

====