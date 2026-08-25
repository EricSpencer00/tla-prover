---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*-----------------------------------------------------------------
\* Constants required by the configuration
\*-----------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*-----------------------------------------------------------------
\* Operator that will be substituted for Succ in the algorithm.
\* It simply returns the same successor mapping but is named
\* differently so the .cfg can replace the original operator.
\*-----------------------------------------------------------------
ConnectedToSomeButNotAll == 
    [n \in Nodes |-> Succ[n]]

\*-----------------------------------------------------------------
\* A finite version of the generic sequence set.  All sequences are
\* limited to length at most |Nodes|, which guarantees a finite state
\* space for model checking.
\*-----------------------------------------------------------------
LimitedSeq(E) == 
    { s \in Seq(E) : Len(s) <= Cardinality(Nodes) }

\*-----------------------------------------------------------------
\* State variables inherited from the sequential reachability algorithm
\*-----------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\*-----------------------------------------------------------------
\* Helper predicate describing a path from Root to a node using the
\* (bounded) successor relation.
\*-----------------------------------------------------------------
PathExists(n) == 
    \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in ConnectedToSomeButNotAll[s[i]]

\*-----------------------------------------------------------------
\* Initial state (the concrete graph is supplied via the constants)
\*-----------------------------------------------------------------
Init == 
    /\ Marked = {Root}
    /\ Frontier = {Root}
    /\ pc = "init"

\*-----------------------------------------------------------------
\* One step of the sequential algorithm: take a node from the frontier,
\* add its successors, and update the frontier.
\*-----------------------------------------------------------------
Next == 
    \/ /\ pc = "init"
       /\ pc' = "run"
       /\ UNCHANGED <<Marked, Frontier>>
    \/ /\ pc = "run"
       /\ Frontier # {}
       /\ \E n \in Frontier :
            LET succs == ConnectedToSomeButNotAll[n] IN
                /\ Marked' = Marked \cup succs
                /\ Frontier' = (Frontier \ {n}) \cup (succs \ Marked)
                /\ pc' = "run"
       /\ UNCHANGED pc
    \/ /\ pc = "run"
       /\ Frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<Marked, Frontier>>

\*-----------------------------------------------------------------
\* Specification of the system
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\*-----------------------------------------------------------------
\* Type correctness invariant
\*-----------------------------------------------------------------
TypeOK == 
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"init", "run", "done"}

\*-----------------------------------------------------------------
\* Invariant 1: every node in the frontier or marked set has its
\* successors either already marked or pending in the frontier.
\*-----------------------------------------------------------------
Inv1 == 
    \A n \in Marked \cup Frontier :
        \A m \in ConnectedToSomeButNotAll[n] :
            m \in Marked \/ m \in Frontier

\*-----------------------------------------------------------------
\* Invariant 2: the root node is always marked.
\*-----------------------------------------------------------------
Inv2 == Root \in Marked

\*-----------------------------------------------------------------
\* Invariant 3: the set of marked nodes coincides with the nodes
\* reachable via bounded paths from the root.
\*-----------------------------------------------------------------
Inv3 == 
    \A n \in Nodes : (n \in Marked) <=> PathExists(n)

\*-----------------------------------------------------------------
\* Partial correctness: when the algorithm finishes (no frontier),
\* the marked set equals the reachable set.
\*-----------------------------------------------------------------
PartialCorrectness == 
    (Frontier = {}) => 
        \A n \in Nodes : (PathExists(n) => n \in Marked)

\*-----------------------------------------------------------------
\* Liveness property: the algorithm eventually reaches the completed
\* state (frontier empty).
\*-----------------------------------------------------------------
Termination == <> (Frontier = {})

====