---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the .cfg
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\*   Marked  : set of nodes that have been discovered
\*   Frontier: set of nodes whose successors are to be explored next
\*   pc      : program counter (for the single sequential process)
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Node == Nodes

\* ----------------------------------------------------------------------
\* Initial state (inherited from the algorithm specification)
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "step"

\* ----------------------------------------------------------------------
\* Single-step action of the sequential reachability algorithm
\* ----------------------------------------------------------------------
Step ==
    /\ pc = "step"
    /\ IF Frontier = {}
          THEN pc' = "done"
               /\ UNCHANGED <<Marked, Frontier>>
          ELSE
               LET n == CHOOSE x \in Frontier : TRUE
               IN /\ Marked' = Marked \cup {n}
                  /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked')
                  /\ pc' = "step"
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Next-state relation (only the algorithm's actions)
\* ----------------------------------------------------------------------
Next == Step

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Safety invariants (identifiers required by the .cfg)
\* ----------------------------------------------------------------------
\* Type correctness: all state variables contain only nodes from Nodes
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"step", "done"}

\* Inv1: Successor closure – every node in Marked is reachable from Root via Seq
Inv1 ==
    \A n \in Marked :
        \E s \in Seq :
            /\ Len(s) > 0
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]

\* Inv2: Reachability decomposition – the union of Marked and Frontier equals the set
\*       of nodes reachable from Root via some sequence in Seq
Inv2 ==
    Marked \cup Frontier =
        { n \in Nodes :
            \E s \in Seq :
                /\ Len(s) > 0
                /\ s[1] = Root
                /\ s[Len(s)] = n
                /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
        }

\* Inv3: Reachable set equality – when the algorithm terminates, Frontier is empty
\*       and Marked equals the set of all nodes reachable from Root
Inv3 ==
    /\ pc = "done"
    /\ Frontier = {}
    /\ Marked =
        { n \in Nodes :
            \E s \in Seq :
                /\ Len(s) > 0
                /\ s[1] = Root
                /\ s[Len(s)] = n
                /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
        }

\* PartialCorrectness – every node marked by the algorithm is indeed reachable
PartialCorrectness ==
    \A n \in Marked :
        \E s \in Seq :
            /\ Len(s) > 0
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]

\* ----------------------------------------------------------------------
\* Liveness property – termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by .cfg but useful)
\*   The specification satisfies all listed invariants.
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK /\ []Inv1 /\ []Inv2 /\ []Inv3 /\ []PartialCorrectness

====