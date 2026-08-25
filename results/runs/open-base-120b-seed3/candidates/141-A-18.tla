---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,            \* The set of all graph nodes
    Root,             \* The distinguished root node
    Succ              \* A total function giving successors of a node

\* ----------------------------------------------------------------------
\* Helper operator: a finite version of Seq (used only for the Reach operator)
\* The .cfg replaces the standard Seq with LimitedSeq, so we provide it here.
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

\* ----------------------------------------------------------------------
\* Successor operator used by the algorithm.
\* The .cfg substitutes this operator for the name Succ, so we define it in
\* terms of the constant Succ.
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Types of the state variables
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}
    /\ Root \in Nodes
    /\ Succ \in [Nodes -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Reachability operator (set of nodes reachable from a set of start nodes)
\* using finite sequences bounded by LimitedSeq.
RECURSIVE Reach(_)
Reach(S) ==
    LET Paths ==
        { p \in LimitedSeq(Nodes) :
            /\ Len(p) > 0
            /\ p[1] \in S
            /\ \A i \in 1 .. Len(p)-1 : p[i+1] \in ConnectedToSomeButNotAll[p[i]]
        }
    IN { p[Len(p)] : p \in Paths }

\* ----------------------------------------------------------------------
\* Invariant 1: every successor of a marked node is either marked or in frontier
Inv1 ==
    \A n \in marked :
        ConnectedToSomeButNotAll[n] \subseteq (marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 2: reachable from frontier is contained in reachable from (marked ∪ frontier)
Inv2 ==
    Reach(frontier) \subseteq Reach(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: the set of nodes reachable from the root equals marked plus
\* nodes reachable from the frontier.
Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

\* ----------------------------------------------------------------------
\* Partial correctness: when the algorithm stops, marked = reachable from root
PartialCorrectness ==
    (frontier = {} ) => (marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Main transition relation
Next ==
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ \E n \in frontier :
            \/ /\ n \notin marked
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
               /\ pc' = "run"
            \/ /\ n \in marked
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
               /\ pc' = IF frontier' = {} THEN "done" ELSE "run"
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ marked' = marked
       /\ frontier' = frontier
       /\ pc' = "done"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination (when reachable set is finite)
Termination == <> (frontier = {})

\* ----------------------------------------------------------------------
\* The set of invariants to be checked
INVARS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

\* ----------------------------------------------------------------------
\* The property to be checked
PROPS == Termination

====