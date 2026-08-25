---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Bounded sequence operator used instead of the standard Seq
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Successor relation: each node has exactly two deterministic successors
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll == 
    [ n \in Nodes |-> 
        { ((n % Cardinality(Nodes)) + 1),
          (((n + 1) % Cardinality(Nodes)) + 1) } ]

\* ----------------------------------------------------------------------
\* Reachable nodes defined via bounded paths from Root
\* ----------------------------------------------------------------------
Reachable == 
    { n \in Nodes :
        \E s \in LimitedSeq(Nodes) :
            Len(s) > 0 /\ 
            s[1] = Root /\ 
            s[Len(s)] = n /\ 
            \A i \in 1..(Len(s)-1) :
                s[i+1] \in ConnectedToSomeButNotAll[s[i]] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "Init"

\* ----------------------------------------------------------------------
\* Next-state relation (sequential Misra reachability algorithm)
\* ----------------------------------------------------------------------
Next == 
    /\ \/ /\ pc = "Init"
          /\ Marked' = Marked
          /\ Frontier' = {Root}
          /\ pc' = "Step"

       \/ /\ pc = "Step"
          /\ \* expand frontier using the successor relation
             LET NewFrontier == 
                 { n \in Nodes :
                     \E m \in Marked \cup Frontier :
                         n \in ConnectedToSomeButNotAll[m] }
             IN 
                 /\ Marked' = Marked \cup Frontier
                 /\ Frontier' = NewFrontier \ Marked'
                 /\ pc' = IF Frontier' = {} THEN "Done" ELSE "Step"

       \/ /\ pc = "Done"
          /\ UNCHANGED <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* State variables tuple for the temporal operators
\* ----------------------------------------------------------------------
vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"Init", "Step", "Done"}

\* ----------------------------------------------------------------------
\* Algorithm invariants
\* ----------------------------------------------------------------------
Inv1 == \A n \in Marked : n \in Reachable

Inv2 == \A n \in Frontier :
          /\ n \notin Marked
          /\ \E m \in Marked : n \in ConnectedToSomeButNotAll[m]

Inv3 == Marked = Reachable

\* ----------------------------------------------------------------------
\* Partial correctness property
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "Done") => (Marked = Reachable)

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====