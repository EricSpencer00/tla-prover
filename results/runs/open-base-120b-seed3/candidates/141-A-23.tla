---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Operator that will be substituted for Succ in the .cfg file
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\*--------------------------------------------------------------------
\* A finite version of Seq (used for model checking)
\*--------------------------------------------------------------------
CONSTANT MaxLen \* a bound on sequence length
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\*--------------------------------------------------------------------
\* Reachability operator (transitive closure of Succ)
\*--------------------------------------------------------------------
RECURSIVE Reach(_)
Reach(S) ==
    IF S = {} THEN {}
    ELSE
        LET new == UNION { Succ[n] : n \in S } IN
        S \cup Reach(new)

\*--------------------------------------------------------------------
\* Main step actions
\*--------------------------------------------------------------------
AddNode ==
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
    /\ UNCHANGED pc

RemoveNode ==
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc = "Run"
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ AddNode
    \/ RemoveNode
    \/ Terminate

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

\*--------------------------------------------------------------------
\* Invariant 1: successors of marked nodes are in marked or frontier
\*--------------------------------------------------------------------
Inv1 ==
    \A m \in marked : Succ[m] \subseteq marked \cup frontier

\*--------------------------------------------------------------------
\* Invariant 2: union of marked and reachable from frontier equals
\* reachable from marked ∪ frontier
\*--------------------------------------------------------------------
Inv2 ==
    (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

\*--------------------------------------------------------------------
\* Invariant 3: reachable from root equals marked plus reachable from frontier
\*--------------------------------------------------------------------
Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

\*--------------------------------------------------------------------
\* Partial correctness: when terminated, marked = reachable from root
\*--------------------------------------------------------------------
PartialCorrectness ==
    (pc = "Done") => (marked = Reach({Root}))

\*--------------------------------------------------------------------
\* Liveness property: eventual termination
\*--------------------------------------------------------------------
Termination == <> (frontier = {} /\ pc = "Done")

=============================================================================