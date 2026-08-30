---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Misra's BFS variant: marked (visited) and frontier may overlap.
VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Pick any frontier node; nondeterministic choice makes the two cases
\* of the loop reachable from the same state.
Explore(n) ==
  /\ n \in frontier
  /\ marked' = IF n \in marked THEN marked ELSE marked \cup {n}
  /\ frontier' = IF n \in marked
       THEN frontier \ {n}
       ELSE frontier \cup Succ[n]
  /\ pc' = "running"

Done ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == (\E n \in Nodes: Explore(n)) \/ Done

Spec == Init /\ [][Next]_vars

\* SAFETY: partial correctness via three shape lemmas about the
\* reachable-from relation, plus type-checking.
Inv1 ==
  \A x \in marked : (Succ[x] \subseteq marked) \cup frontier

Inv2 ==
  (marked \cup frontier)
    = (marked \cup (Succ[marked \cup frontier] \cup frontier))

Inv3 ==
  (\A x \in frontier : Succ[x] \subseteq marked \cup frontier)
    \cup (Succ[marked] \cup marked) = Nodes

PartialCorrectness ==
  \A x \in Nodes : (x \in marked) <=> (\E k \in Nat : k >= 1 /\ \E f \in [1..k -> Nodes] :
    /\ f[1] = Root
    /\ \A i \in 1..(k - 1) : x \in Succ[f[i]]
    /\ f[k] = x)

\* LIVENESS: fairness + finiteness of the reachable set forces eventual
\* termination of the loop.
Termination ==
  \A x \in Nodes : (x \in Succ[Root]) ~> (x \notin frontier)

\* The .cfg substitutes these in: Succ is replaced by a bounded/out degree
\* version, and Seq (LimitedSeq below) is replaced by a finite stub so
\* the model stays checkable.
ConnectedToSomeButNotAll == {n \in Nodes : Succ[n] # {}}
LimitedSeq == Sequences.Seq

====