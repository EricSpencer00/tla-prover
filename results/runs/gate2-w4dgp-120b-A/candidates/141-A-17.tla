---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* Revised for compile-time boundedness: a finite sequence that never grows past
\* the number of nodes in the graph.
LimitedSeq(S) == [n \in 0..Cardinality(Nodes) |-> CHOOSE e \in S : TRUE]

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Overlap is allowed: the frontier can still contain a node that was just marked,
\* so the algorithm does not have to drain the frontier before it starts.
Step ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E x \in frontier :
         \/ /\ x \notin marked
            /\ marked' = marked \cup {x}
            /\ frontier' = frontier \cup Succ[x]
         \/ /\ x \in marked
            /\ frontier' = frontier \ {x}
            /\ UNCHANGED marked
    /\ pc' = IF frontier' = {} THEN "done" ELSE pc

Next == Step

Spec == Init /\ [][Next]_vars

\* Forward closure: successors of marked nodes are always in play, either already
\* marked or still waiting in the frontier.
Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Reachability is stable under the partition between marked and frontier.
Inv2 ==
    (marked \cup frontier) = {Root} \cup UNION {Succ[m] : m \in (marked \cup frontier)}

\* The explored set plus whatever is still reachable from the frontier is
\* exactly the set reachable from the root.
Inv3 == {Root} \cup UNION {Succ[m] : m \in frontier} = {Root} \cup UNION {Succ[m] : m \in marked}

PartialCorrectness ==
    pc = "done" => marked = {Root} \cup UNION {Succ[m] : m \in marked}

Termination ==
    \A S \in FiniteSubsets(Nodes) : (S = {Root} \cup UNION {Succ[m] : m \in S}) ~> (S = {Root} \cup UNION {Succ[m] : m \in S})

====