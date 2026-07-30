---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

\* Misra's overlapping-set BFS: marked and frontier may both contain a node.
vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

RECURSIVE ReachableSet(_)
ReachableSet(S) ==
  IF S = {} THEN {}
  ELSE
    LET x == CHOOSE y \in S : TRUE
        rest == S \ {x}
    IN {x} \cup (Succ[x] \cup ReachableSet(rest))

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The main action, with its two (nondeterministic) cases.
Step ==
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step) /\ WF_vars(Terminate)

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup ReachableSet(frontier) = ReachableSet(marked \cup frontier)

Inv3 ==
  ReachableSet(Nodes) = marked \cup ReachableSet(frontier)

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) <=> (n \in ReachableSet({Root}))

Termination == (ReachableSet(Nodes) # {}) ~> (pc = "done")

\* Operators that the .cfg substitutes in at model-check time.
ConnectedToSomeButNotAll == ConnectedToSomeButNotAll

\* The .cfg replaces Seq with this bounded version for finite models.
LimitedSeq == (LimitedSeq :> Sequences.Seq)
====