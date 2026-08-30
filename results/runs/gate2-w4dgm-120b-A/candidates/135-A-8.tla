---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "running"

Mark(n) ==
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ[n]) \ marked'
  /\ pc' = pc

Skip(n) ==
  /\ n \in frontier
  /\ n \in marked
  /\ frontier' = (frontier \cup Succ[n]) \ marked'
  /\ pc' = pc
  /\ marked' = marked

MarkAny == \E n \in Nodes : Mark(n)
SkipAny == \E n \in Nodes : Skip(n)

Next == MarkAny \/ SkipAny \/ (pc' = "done" /\ UNCHANGED <<marked, frontier, pc>>)

Spec == Init /\ [][Next]_vars /\ WF_vars(MarkAny) /\ WF_vars(SkipAny)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \A n \in frontier : \A m \in marked : m \notin Succ[n]

Inv2 ==
  \A n \in marked : n \in Succ[Root]

Inv3 ==
  \A n \in marked : n \in ConnectedToSomeButNotAll

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) = (\E s \in LimitedSeq(Nodes) : s[1] = Root /\ s[Len(s)] = n)

Termination ==
  <>(pc = "done")

\* Each node is connected to exactly two others, so the closure of the root is
\* not trivially the whole set; still finite, keeping the model checkable.
ConnectedToSomeButNotAll == UNION {Succ[n] : n \in Nodes}

\* Reachability is an existential path search, but the paths of interest are
\* bounded by the number of nodes, and with the node set fixed this yields a
\* finite, model-checkable definition of Reachable.
LimitedSeq(S) ==
  {s \in Seq(S) : Len(s) <= Cardinality(Nodes)}

====