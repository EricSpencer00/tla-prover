---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Bounded sequence operator (replaces the infinite Seq)
\*--------------------------------------------------------------------
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* Successor function limited to exactly two distinct successors per node
\* (substituted for the generic Succ operator)
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  IF n \in Nodes THEN
    CHOOSE s \in SUBSET Nodes :
      /\ Cardinality(s) = 2
      /\ n \notin s
  ELSE {}

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

\*--------------------------------------------------------------------
\* One step of the sequential Misra reachability algorithm
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "run"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ marked')
          /\ pc' = IF frontier' = {} THEN "done" ELSE "run"
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}
  /\ \A n \in Nodes : Cardinality(ConnectedToSomeButNotAll(n)) = 2

\*--------------------------------------------------------------------
\* Invariant 1: successor closure
\*--------------------------------------------------------------------
Inv1 ==
  \A n \in marked :
    ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

\*--------------------------------------------------------------------
\* Invariant 2: reachability decomposition (Root is always reachable)
\*--------------------------------------------------------------------
Inv2 ==
  Root \in marked \cup frontier

\*--------------------------------------------------------------------
\* Invariant 3: reachable set equality at termination
\*--------------------------------------------------------------------
Inv3 ==
  (pc = "done") => 
    \A n \in Nodes :
      ( \E s \in LimitedSeq :
          /\ Len(s) > 0
          /\ s[1] = Root
          /\ s[Len(s)] = n
          /\ \A i \in 1..(Len(s)-1) :
                s[i+1] \in ConnectedToSomeButNotAll(s[i])
      ) => n \in marked

\*--------------------------------------------------------------------
\* Partial correctness: when done, all reachable nodes are marked
\*--------------------------------------------------------------------
PartialCorrectness ==
  (pc = "done") => marked = { n \in Nodes :
                               \E s \in LimitedSeq :
                                 /\ Len(s) > 0
                                 /\ s[1] = Root
                                 /\ s[Len(s)] = n
                                 /\ \A i \in 1..(Len(s)-1) :
                                      s[i+1] \in ConnectedToSomeButNotAll(s[i])
                             }

\*--------------------------------------------------------------------
\* Liveness property: termination
\*--------------------------------------------------------------------
Termination ==
  <> (pc = "done")

====