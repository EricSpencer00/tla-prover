---- MODULE Reachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Pick a frontier node nondeterministically; the frontier may keep an already
\* visited node, which is what distinguishes this variant from standard BFS.
Step ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

\* (1) Every successor of a marked node is either already marked or still in the
\* frontier to be explored next; this is what makes the frontier sticky.
Inv1 ==
  \A n, m \in Nodes : (n \in marked /\ m \in Succ[n]) => (m \in marked \/ m \in frontier)

\* (2) The marked nodes plus the nodes reachable from the frontier together
\* reach everything reachable from their union -- frontier nodes can still pull
\* new nodes into the reachable set because visited nodes may stay in the frontier.
Inv2 ==
  (marked) \cup (UNION {UNION {Succ[m] : m \in frontier}}) = (marked \cup frontier)

\* (3) The nodes reachable from the root are exactly the marked nodes plus the
\* nodes reachable from whatever is still in the frontier.
Inv3 ==
  (UNION {Succ[n] : n \in {Root}}) = marked \cup (UNION {UNION {Succ[m] : m \in frontier}})

PartialCorrectness ==
  pc = "terminated" => (marked = (UNION {Succ[n] : n \in {Root}}))

Termination ==
  (\A n \in Nodes : Cardinality(Succ[n]) < 2) ~> (pc = "terminated")

\* The .cfg for the standard TLA+ library replaces Seq with a finite version for
\* this module's scope. The operator name on the left is the one overridden.
LimitedSeq == LimitedSeq

ConnectedToSomeButNotAll == ConnectedToSomeButNotAll

====