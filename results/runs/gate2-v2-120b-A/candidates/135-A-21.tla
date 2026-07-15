---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------
\* Constants required by the .cfg file
\* -------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* -------------------------------------------------
\* Derived sets and functions
\* -------------------------------------------------
NodeSet == Nodes

\* For each node n, Succ[n] is the set of its two successors.
SuccSet == [n \in NodeSet |-> Succ[n]]

\* -------------------------------------------------
\* State variables (same as in the sequential reachability algorithm)
\* -------------------------------------------------
VARIABLES Marked, Frontier, pc

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
\* The set of all finite sequences (of length ≤ Cardinality(NodeSet))
\* composed of nodes, respecting the override Seq.
AllSeq == { s \in Seq :
             Len(s) <= Cardinality(NodeSet) /\ 
             /\ \A i \in 1..Len(s) : s[i] \in NodeSet
            }

\* -------------------------------------------------
\* Initial state (inherited from the algorithm, instantiated with the concrete graph)
\* -------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "Init"

\* -------------------------------------------------
\* Next-state relation (inherits algorithm actions)
\* -------------------------------------------------
Next ==
    \/ \E n \in Frontier :
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (SuccSet[n] \ Marked')
          /\ pc' = "Step"
    \/ /\ Marked' = Marked
       /\ Frontier' = {}
       /\ pc' = "Done"
    \/ UNCHANGED <<Marked, Frontier, pc>>

\* -------------------------------------------------
\* Specification formula (required name: Spec)
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* -------------------------------------------------
\* Type correctness invariant (required name: TypeOK)
\* -------------------------------------------------
TypeOK ==
    /\ Marked \subseteq NodeSet
    /\ Frontier \subseteq NodeSet
    /\ pc \in {"Init", "Step", "Done"}

\* -------------------------------------------------
\* Algorithm invariants (required names: Inv1, Inv2, Inv3)
\* -------------------------------------------------
\* Inv1: Successor closure – every node in Frontier has all its successors
\* (that are not yet marked) also in Frontier or Marked.
Inv1 ==
    \A n \in Frontier :
        SuccSet[n] \subseteq Marked \cup Frontier

\* Inv2: Reachability decomposition – every marked node is reachable from Root
\* via a sequence in AllSeq.
Inv2 ==
    \A n \in Marked :
        \E s \in AllSeq :
            /\ Len(s) >= 1
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in SuccSet[s[i]]

\* Inv3: Reachable set equality – the set of nodes reachable from Root
\* via any sequence in AllSeq equals Marked ∪ Frontier.
Reachable ==
    { n \in NodeSet :
        \E s \in AllSeq :
            /\ Len(s) >= 1
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in SuccSet[s[i]]
    }

Inv3 == Reachable = Marked \cup Frontier

\* -------------------------------------------------
\* Partial correctness property (required name: PartialCorrectness)
\* -------------------------------------------------
PartialCorrectness ==
    (pc = "Done") => (Marke

d = NodeSet)

\* -------------------------------------------------
\* Termination liveness property (required name: Termination)
\* -------------------------------------------------
Termination == <> (pc = "Done")

====