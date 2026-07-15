---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* State variables inherited from the sequential reachability algorithm
\*   Marked   : the set of nodes already discovered as reachable
\*   Frontier : the set of nodes whose successors still need to be explored
\*   pc       : program counter indicating which step of the algorithm we are in
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NodeSet == Nodes
SeqSet  == Seq

\* ----------------------------------------------------------------------
\* Safety invariant: all variables stay within their intended domains
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq NodeSet
  /\ Frontier \subseteq NodeSet
  /\ pc \in {"Init", "Step", "Done"}

\* ----------------------------------------------------------------------
\* Algorithm invariants (place‑holders that capture the intended properties)
\* ----------------------------------------------------------------------
Inv1 == Marked \subseteq NodeSet

Inv2 ==
  /\ \A n \in Marked : 
        \E i \in 1..Len(Seq) :
          Seq[i] = n
  /\ \A i \in 1..Len(Seq) :
        Len(Seq) <= Cardinality(NodeSet)

Inv3 ==
  /\ \A n \in NodeSet :
        (n \in Marked) => 
          \E m \in Marked : n \in Succ[m]

PartialCorrectness ==
  /\ pc = "Done"
  /\ Marked = { n \in NodeSet : \E m \in NodeSet : n \in Succ[m]^* }

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "Init"

\* ----------------------------------------------------------------------
\* One iteration of the algorithm
\* ----------------------------------------------------------------------
Step ==
  /\ pc = "Init"
  /\ Marked' = {Root}
  /\ Frontier' = Succ[Root]
  /\ pc' = "Step"

Explore ==
  /\ pc = "Step"
  /\ IF Frontier = {} 
        THEN /\ Marked' = Marked
             /\ Frontier' = {}
             /\ pc' = "Done"
        ELSE 
        LET n == CHOOSE x \in Frontier : TRUE IN
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup Succ[n]
        /\ pc' = "Step"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ Step \/ Explore

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Liveness property: the algorithm eventually terminates
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

=============================================================================