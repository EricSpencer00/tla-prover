---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* A concrete graph: each node points to exactly two successors, chosen
\* deterministically to keep the model finite and non-trivial.
NodeCount == 4
SuccCount == 2

SuccOf(n) == CASE n = 1 -> {2, 3}
              [] n = 2 -> {3, 4}
              [] n = 3 -> {1, 4}
              [] n = 4 -> {1, 2}
              [] OTHER -> {}

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = SuccOf(Root)
  /\ pc = "running"

Expand(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ frontier' = (frontier \cup SuccOf(n)) \ marked
  /\ marked' = marked \cup {n}
  /\ UNCHANGED pc

Complete ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Reset ==
  /\ pc = "done"
  /\ marked' = {Root}
  /\ frontier' = SuccOf(Root)
  /\ pc' = "running"

Next ==
  \/ \E n \in Nodes : Expand(n)
  \/ Complete
  \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Complete)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

\* Successor closure of the marked region: any node reachable from a marked
\* node is already marked, so no reachable node is ever left out.
Inv1 == \A n \in marked : SuccOf(n) \subseteq marked

\* Reachability decomposition: the marked set plus the frontier (nodes
\* adjacent to some marked node but not yet marked) cover the whole graph.
Inv2 == marked \cup frontier = Nodes

\* Reachable-set equality: every node is reachable from the root exactly
\* when it is marked, so no reachable node is omitted from the marked set.
Inv3 == {n \in Nodes : \E k \in Nat : \E s \in LimitedSeq(Nodes) :
            /\ Len(s) = k
            /\ s[1] = Root
            /\ s[k] = n
            /\ \A i \in 1..(k - 1) : s[i + 1] \in SuccOf(s[i])}
        = marked

PartialCorrectness == \A n \in Nodes : n \notin marked => \A k \in Nat : \A s \in LimitedSeq(Nodes) :
                        Len(s) = k /\ s[1] = Root /\ s[k] = n
                          => \E i \in 1..(k - 1) : s[i + 1] \notin SuccOf(s[i])

Termination == <>(pc = "done")

\* Model-checking-friendly overrides of operators from the standard modules,
\* keeping the exact names the .cfg expects (substituted on the right side).
ConnectedToSomeButNotAll == SuccOf
LimitedSeq(S) == {s \in Seq(S) : Len(s) <= NodeCount}
====