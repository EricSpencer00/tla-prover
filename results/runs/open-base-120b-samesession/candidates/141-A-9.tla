---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS
    Nodes,          \* The set of all nodes in the graph
    Root,           \* The distinguished root node
    Succ            \* Binary relation defining edges (may be overridden)

\* ----------------------------------------------------------------------
\* Operator that may replace Succ in the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == 
    { m \in Nodes : <<n, m>> \in Succ }

\* ----------------------------------------------------------------------
\* A finite version of Seq for model checking
\* ----------------------------------------------------------------------
MaxLen == 5
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Helper: set of nodes reachable from a set of source nodes via Succ
\* ----------------------------------------------------------------------
ReachSet(S) == 
    { n \in Nodes : \E s \in S : <<s, n>> \in TC(Succ) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Run"

\* ----------------------------------------------------------------------
\* Main transition relation
\* ----------------------------------------------------------------------
Explore ==
    /\ frontier # {}
    /\ \E n \in frontier:
        \/ /\ n \notin marked
              /\ marked'   = marked \cup {n}
              /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
              /\ pc'       = pc
        \/ /\ n \in marked
              /\ marked'   = marked
              /\ frontier' = frontier \ {n}
              /\ pc'       = pc
        /\ UNCHANGED << >>

Done ==
    /\ frontier = {}
    /\ pc'       = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Invariant 1: every successor of a marked node is in marked ∪ frontier
\* ----------------------------------------------------------------------
Inv1 ==
    \A n \in marked : ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ Reach(frontier) = Reach(marked ∪ frontier)
\* ----------------------------------------------------------------------
Inv2 ==
    marked \cup ReachSet(frontier) = ReachSet(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: Reach({Root}) = marked ∪ Reach(frontier)
\* ----------------------------------------------------------------------
Inv3 ==
    ReachSet({Root}) = marked \cup ReachSet(frontier)

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated, marked = all nodes reachable from Root
\* ----------------------------------------------------------------------
PartialCorrectness ==
    pc = "Done" => marked = ReachSet({Root})

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES == Termination

====