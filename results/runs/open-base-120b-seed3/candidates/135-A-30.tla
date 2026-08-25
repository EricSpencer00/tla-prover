---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Concrete graph: 4 nodes, each with exactly 2 successors.
\* ----------------------------------------------------------------------
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root \in Nodes

ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  [] n = 2 -> {1, 4}
  [] n = 3 -> {1, 4}
  [] n = 4 -> {2, 3}
  [] OTHER -> {}

\* ----------------------------------------------------------------------
\* Limited version of Seq for model checking (bounded by |Nodes|).
\* ----------------------------------------------------------------------
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Helper definition of the set of nodes reachable from Root using
\* paths of length at most |Nodes|.
\* ----------------------------------------------------------------------
ReachableSet ==
  { n \in Nodes :
      \E s \in LimitedSeq :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..(Len(s) - 1) :
            s[i+1] \in ConnectedToSomeButNotAll(s[i])
  }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "init"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "init"
     /\ pc' = "step"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "step"
     /\ Frontier # {}
     /\ \E n \in Frontier :
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked')
          /\ pc' = "step"
          /\ UNCHANGED <<>>
  \/ /\ pc = "step"
     /\ Frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

Inv1 ==
  \A n \in Marked :
    ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

Inv2 ==
  Frontier \subseteq Nodes \ Marked

Inv3 ==
  Marked = ReachableSet

PartialCorrectness ==
  pc = "done" => Marked = ReachableSet

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS == TypeOK, Inv1, Inv2, Inv3, PartialCorrectness
PROPERTIES  == Termination

====