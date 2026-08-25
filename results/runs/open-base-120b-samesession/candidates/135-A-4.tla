---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Concrete graph used for model checking.
\* The configuration replaces Succ with ConnectedToSomeButNotAll,
\* so we provide a bounded successor operator.
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2,3}
  []  n = 2 -> {3,4}
  []  n = 3 -> {1,4}
  []  n = 4 -> {1,2}
  []  OTHER -> {}

\*--------------------------------------------------------------------
\* Finite version of the generic sequence type.
\* The configuration replaces Seq with LimitedSeq.
\*--------------------------------------------------------------------
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables of the sequential Misra reachability algorithm
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Initial state (inherited, instantiated with the concrete graph)
\*--------------------------------------------------------------------
Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "Init"

\*--------------------------------------------------------------------
\* Transition relation (same as the algorithm specification)
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "Init"
     /\ pc' = "Step"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "Step"
     /\ frontier # {}
     /\ \E n \in frontier :
          LET succs == Succ[n] \* (will be substituted by ConnectedToSomeButNotAll)
              newFrontier == (frontier \ {n}) \cup (succs \ marked)
          IN /\ marked'   = marked \cup succs
             /\ frontier' = newFrontier
             /\ pc'       = "Step"
             /\ UNCHANGED {}
  \/ /\ pc = "Step"
     /\ frontier = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<marked, frontier>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Invariants required by the configuration
\*--------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Init","Step","Done"}

Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
  \A n \in marked :
    \E s \in LimitedSeq :
      /\ Len(s) >= 1
      /\ s[1] = Root
      /\ Last(s) = n
      /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]

Inv3 ==
  \A n \in Nodes :
    ( \E s \in LimitedSeq :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ Last(s) = n
        /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
    ) \iff n \in marked \cup frontier

PartialCorrectness ==
  (pc = "Done") =>
    marked = { n \in Nodes :
                \E s \in LimitedSeq :
                  /\ Len(s) >= 1
                  /\ s[1] = Root
                  /\ Last(s) = n
                  /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

\*--------------------------------------------------------------------
\* Liveness property (termination)
\*--------------------------------------------------------------------
Termination == <> (pc = "Done")

====