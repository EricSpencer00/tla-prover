---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Concrete graph: each node has exactly two successors.
\* The .cfg substitutes this operator for the abstract Succ.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  LET
    sz == Cardinality(Nodes)
  IN
    LET
      s1 == (n % sz) + 1
    IN
      LET
        s2 == ((n + 1) % sz) + 1
      IN { s1, s2 }

\* ----------------------------------------------------------------------
\* Bounded sequences used in reachability definitions.
\* The .cfg substitutes this operator for Seq.
\* ----------------------------------------------------------------------
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Initial state (concrete instance of the algorithm's Init)
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = { Root }
  /\ pc = "init"

\* ----------------------------------------------------------------------
\* Next-state relation (concrete instance of the algorithm's Next)
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "init"
     /\ pc' = "step"
     /\ UNCHANGED << marked, frontier >>
  \/ /\ pc = "step"
     /\ \E n \in frontier :
          /\ marked' = marked \cup { n }
          /\ frontier' = (frontier \ { n }) \cup ConnectedToSomeButNotAll[n] \ marked
          /\ pc' = IF frontier' = {} THEN "done" ELSE "step"
     /\ UNCHANGED pc
  \/ /\ pc = "done"
     /\ UNCHANGED << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\* Variables tuple for the temporal operator
\* ----------------------------------------------------------------------
vars == << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\* Specification formula required by the .cfg
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg
\* ----------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

Inv1 ==  \* successor closure for nodes in the frontier
  \A n \in frontier :
    \A s \in ConnectedToSomeButNotAll[n] :
      s \in marked

Inv2 ==  \* frontier is always a subset of Nodes
  frontier \subseteq Nodes

Inv3 ==  \* marked is always a subset of Nodes
  marked \subseteq Nodes

Reachable ==
  { n \in Nodes :
      \E seq \in LimitedSeq :
        /\ Len(seq) >= 1
        /\ seq[1] = Root
        /\ seq[Len(seq)] = n
        /\ \A i \in 1 .. Len(seq)-1 :
             seq[i+1] \in ConnectedToSomeButNotAll[seq[i]] }

PartialCorrectness ==
  (pc = "done") => (marked = Reachable)

\* ----------------------------------------------------------------------
\* Liveness property required by the .cfg
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

====