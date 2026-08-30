---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Succ is a graph's successor-set function; the .cfg substitutes a
\* bounded definition for it, so we need not provide one here.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE Reaches(_)
Reaches(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN Succ[x] \cup Reaches(S \ {x})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "halted"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The two cases: expand an unmarked node, or pull an already-marked one
\* out of the frontier. The marked and frontier sets may overlap throughout.
Step ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E x \in frontier :
       IF x \notin marked
         THEN /\ marked' = marked \cup {x}
              /\ frontier' = frontier \cup Succ[x]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {x}
  /\ UNCHANGED pc

Halt ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "halted"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Halt

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Every successor of a marked node is either already marked or is still
\* waiting in the frontier; nothing reachable is ever dropped.
Inv1 ==
  \A x \in marked : Succ[x] \subseteq marked \cup frontier

\* The combined reachable frontier of the two sets is the same as the
\* reachable frontier of their union -- no node reachable from either set
\* is ever left behind by the overlap.
Inv2 ==
  Reaches(marked \cup frontier) = Reaches(marked) \cup Reaches(frontier)

Inv3 ==
  \A x \in frontier : Succ[x] \subseteq (marked \cup frontier)

PartialCorrectness ==
  \A x \in Nodes : (x \in Reaches({Root}) <=> x \in marked)

Termination == pc = "halted"

\* A bounded version of Seq, used by the TLC configuration in place of the
\* standard (possibly infinite) definition from Sequences.
LimitedSeq == Sequences.LimitedSeq

====