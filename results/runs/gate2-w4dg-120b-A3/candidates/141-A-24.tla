---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

Explore ==
  /\ frontier # {}
  /\ pc' = "running"
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ UNCHANGED pc

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Explore
  \/ Terminate

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Explore)
  /\ WF_vars(Terminate)

ReachableFrom(S) ==
  LET f[T \in SUBSET Nodes] ==
        IF T = {} THEN {}
        ELSE LET n == CHOOSE x \in T : TRUE
             IN Succ[n] \cup f[T \ {n}]
  IN f[S]

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom({Root}))

Termination == (pc = "done")

LimitedSeq ==
  [Head |-> CHOOSE s \in Seq(Nodes) : TRUE, Tail |-> <<>>]

ConnectedToSomeButNotAll ==
  {n \in Nodes : Cardinality(ConnectedToSomeButNotAll[n]) > 0}

====