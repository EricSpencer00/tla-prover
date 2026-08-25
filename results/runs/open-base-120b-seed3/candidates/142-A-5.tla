---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC, SeqReachAlg, ReachabilityLemmas

CONSTANTS
    Nodes,
    Root

VARIABLES
    Marked,        \* set of nodes already marked as reachable
    Frontier,      \* set of nodes on the frontier
    pc             \* program counter of the sequential algorithm

\* ----------------------------------------------------------------------
\* Helper definitions (assumed to be provided by the extended modules)
\* ----------------------------------------------------------------------
Succ == SeqReachAlg!Succ               \* successor function on nodes
Reachable == ReachabilityLemmas!Reachable   \* reachability operator
Lemma1 == ReachabilityLemmas!Lemma1
Lemma2 == ReachabilityLemmas!Lemma2
Lemma3 == ReachabilityLemmas!Lemma3

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeCorrect ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"init", "step", "done"}

\* ----------------------------------------------------------------------
\* Invariant 1: inductive type correctness and successor property
\* ----------------------------------------------------------------------
Invariant1 ==
    /\ TypeCorrect
    /\ \A n \in Marked :
          \A s \in Succ[n] : s \in Marked \/ s \in Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: relationship between marked set, frontier and reachability
\* ----------------------------------------------------------------------
Invariant2 ==
    (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: reachable set from the root
\* ----------------------------------------------------------------------
Invariant3 ==
    Reachable({Root}) = Marked \cup Reachable(Frontier)

\* ----------------------------------------------------------------------
\* INITIAL STATE (delegated to the algorithm module)
\* ----------------------------------------------------------------------
INIT ==
    SeqReachAlg!Init

\* ----------------------------------------------------------------------
\* NEXT STATE RELATION (delegated to the algorithm module)
\* ----------------------------------------------------------------------
NEXT ==
    SeqReachAlg!Next

\* ----------------------------------------------------------------------
\* Specification of the system
\* ----------------------------------------------------------------------
Spec ==
    /\ INIT
    /\ [][NEXT]_<\<Marked, Frontier, pc\>>

\* ----------------------------------------------------------------------
\* The required identifiers for the TLC configuration
\* ----------------------------------------------------------------------
SPECIFICATION == Spec

INVARIANTS == <<Invariant1, Invariant2, Invariant3>>

PROPERTIES == <<Spec>>

====