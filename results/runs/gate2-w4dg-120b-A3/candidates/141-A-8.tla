---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Replaced per the .cfg: ConnectedToSomeButNotAll replaces Succ
ConnectedToSomeButNotAll(n) == Succ[n]

\* Replaced per the .cfg: LimitedSeq replaces the infinite Seq from Sequences
LimitedSeq(S) == CHOOSE seq \in { x \in Seq(S) : Cardinality(SetOfSeq(x)) < Cardinality(S) + 1 } : TRUE

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* The loop's choice between the two cases is nondeterministic; each is
\* applied only when its guard (n \in frontier) holds.
Loop ==
  /\ pc = "start"
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = "start"

Done ==
  /\ frontier = {}
  /\ pc = "done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == Loop \/ Done

Spec == Init /\ [][Next]_vars

\* (1) A marked node's successors are at least reachable from the current view.
Inv1 == \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq (marked \cup frontier)

\* (2) The marked-plus-frontier reachability merges cleanly.
Inv2 ==
  \A S \in (SUBSET Nodes) :
    (S \cup (UNION { ConnectedToSomeButNotAll[n] : n \in S })) \cup
       (frontier \cup (UNION { ConnectedToSomeButNotAll[n] : n \in frontier })) =
    (S \cup frontier) \cup (UNION { ConnectedToSomeButNotAll[n] : n \in (S \cup frontier) })

\* (3) The root's reachability splits between marked and frontier.
Inv3 ==
  \A S \in (SUBSET Nodes) :
    ConnectedToSomeButNotAll[n] \in (S \cup (UNION { ConnectedToSomeButNotAll[n] : n \in S })) =
    (S \cup frontier) \cup (UNION { ConnectedToSomeButNotAll[n] : n \in (S \cup frontier) })

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) <=> (n \in ConnectedToSomeButNotAll[Root])

Termination ==
  \A reachable \in SUBSET Nodes :
     (\A n \in reachable : n \in Nodes) ~> (frontier = {})

====