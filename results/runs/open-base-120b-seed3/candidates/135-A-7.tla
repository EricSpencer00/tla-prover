---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Operator overriding the generic successor relation.
\* The configuration substitutes this for the identifier Succ.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Finite version of Seq used to bound path lengths.
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Helper definition of the set of nodes reachable from the root
\* using bounded paths.
\* ----------------------------------------------------------------------
ReachableFromRoot ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 :
             s[i+1] \in ConnectedToSomeButNotAll(s[i])
  }

\* ----------------------------------------------------------------------
\* Initial state (inherits the algorithm's initialization).
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "start"

\* ----------------------------------------------------------------------
\* Next-state relation (inherits the algorithm's actions).
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "start"
     /\ pc' = "run"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "run"
     /\ \E n \in Frontier :
          /\ n \notin Marked
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \cup ConnectedToSomeButNotAll(n)) \ {n}
          /\ UNCHANGED pc
  \/ /\ pc = "run"
     /\ \A n \in Frontier : n \in Marked
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>

\* ----------------------------------------------------------------------
\* Specification formula required by the .cfg file.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file.
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"start", "run", "done"}

Inv1 ==
  /\ \A n \in Marked :
        \A m \in ConnectedToSomeButNotAll(n) : m \in Nodes
  /\ \A n \in Frontier :
        \A m \in ConnectedToSomeButNotAll(n) : m \in Nodes

Inv2 ==
  /\ Frontier = { n \in Nodes :
                    n \notin Marked /\
                    \E p \in LimitedSeq(Nodes) :
                      /\ Len(p) > 0
                      /\ p[1] = Root
                      /\ p[Len(p)] = n
                      /\ \A i \in 1..Len(p)-1 :
                           p[i+1] \in ConnectedToSomeButNotAll(p[i])
                }
  /\ Marked \subseteq ReachableFromRoot

Inv3 == Marked = ReachableFromRoot

PartialCorrectness == (pc = "done") => (Marked = ReachableFromRoot)

\* ----------------------------------------------------------------------
\* Liveness property: the algorithm eventually terminates.
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

====