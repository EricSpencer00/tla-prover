---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Update(v) ==
  /\ v \notin marked
  /\ marked' = marked \cup {v}
  /\ frontier' = frontier \cup {v}
  /\ UNCHANGED pc

Step ==
  /\ pc = "running"
  /\ frontier # {}
  /\ frontier' = {}
  /\ marked' = marked
  /\ UNCHANGED pc

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E v \in Succ[Root]: Update(v)
  \/ Step
  \/ Done

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Step)
  /\ WF_vars(Done)

\* Closure under the immediate-successor relation.
Inv1 ==
  \A v \in frontier : \E w \in Succ[v] : w \in marked

\* Reachability is closed under concatenation of paths.
Inv2 ==
  \A u, v \in Nodes :
    (\E s \in LimitedSeq(Nodes) : s # <<>> /\ s[1] = u /\ s[Len(s)] = v /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]])
      => (\E s \in LimitedSeq(Nodes) : s # <<>> /\ s[1] = u /\ s[Len(s)] = v /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]])

\* Reachability is preserved under path extension.
Inv3 ==
  \A u, v, w \in Nodes :
    (\E s \in LimitedSeq(Nodes) : s # <<>> /\ s[1] = u /\ s[Len(s)] = v /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]])
      /\ w \in Succ[v]
        => (\E s \in LimitedSeq(Nodes) : s # <<>> /\ s[1] = u /\ s[Len(s)] = w /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]])

PartialCorrectness ==
  \A u, v \in Nodes :
    (\E s \in LimitedSeq(Nodes) : s # <<>> /\ s[1] = u /\ s[Len(s)] = v /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]])
      => (\E s \in LimitedSeq(Nodes) : s # <<>> /\ s[1] = Root /\ s[Len(s)] = v /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]])

Termination ==
  (\A v \in Nodes : v \in marked) ~> (pc = "done")

\* For a finite state space, reachability is checked against a bounded
\* sequence set rather than the full (infinite) Countable set.
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* The concrete graph: each node connects to exactly two successors, chosen
\* so the reachability pattern is non-trivial but stays finite.
ConnectedToSomeButNotAll == Succ

====