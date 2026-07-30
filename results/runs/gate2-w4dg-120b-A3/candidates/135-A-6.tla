---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* The standard reachability algorithm has an internal Sequences.Seq used to
\* express "there exists a path from Root to x".  That Seq is infinite, so the
\* model checker cannot explore it.  The .cfg substitutes the operator
\* LimitedSeq for it, which is a finite version; the operator name on the
\* left (LimitedSeq) is replaced by the right-hand side, so we must define
\* LimitedSeq here and must NOT declare Seq itself.

\* A finite Seq: any sequence that has reached the length bound is stuck at its
\* maximum rather than growing forever.
LimitedSeq(T) == UNION { { s \in Seq(T) : Len(s) <= Cardinality(Nodes) } }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Start ==
  /\ pc = "idle"
  /\ pc' = "running"
  /\ UNCHANGED <<marked, frontier>>

MarkStep ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ x \notin marked
       /\ marked' = marked \cup {x}
       /\ frontier' = (frontier \cup (Succ[x] \ {x})) \ {x}
  /\ UNCHANGED pc

Finish ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Start \/ MarkStep \/ Finish

Spec == Init /\ [][Next]_vars

Inv1 == marked \subseteq (UNION { Succ[x] : x \in Nodes })
Inv2 == marked = (UNION { Succ[x] : x \in marked })
Inv3 == marked \cup frontier = Nodes

PartialCorrectness == \A x \in Nodes : \E s \in LimitedSeq(Nodes) :
  /\ s # <<>>
  /\ Head(s) = Root
  /\ Last(s) = x
  /\ \A i \in 1 .. (Len(s) - 1) : s[i + 1] \in Succ[s[i]]

Termination == <>(pc = "done")

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, giving each node
\* exactly two successors.  Here we declare the operator that will be used in
\* that substitution; the name on the left is what the .cfg replaces.
ConnectedToSomeButNotAll ==
  [x \in Nodes |-> Succ[x]]

====