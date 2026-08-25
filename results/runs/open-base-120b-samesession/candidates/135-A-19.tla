---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* Concrete graph definition (overridden by the .cfg via ConnectedToSomeButNotAll)
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 1 -> {2,3}
       [] n = 2 -> {3,4}
       [] n = 3 -> {4,1}
       [] n = 4 -> {1,2}
  ]

\*--------------------------------------------------------------------
\* Bounded sequence operator (replaces Seq from Sequences)
\*--------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables of the sequential reachability algorithm
\*--------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

\*--------------------------------------------------------------------
\* Helper: set of nodes reachable from Root using the (bounded) successor relation
\*--------------------------------------------------------------------
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
  }

\*--------------------------------------------------------------------
\* Initial state (inherits from the algorithm specification)
\*--------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "init"

\*--------------------------------------------------------------------
\* Next-state relation (standard BFS‑style reachability algorithm)
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "init"
     /\ pc' = "step"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "step"
     /\ Frontier # {}
     /\ \E n \in Frontier :
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \cup Succ[n]) \ Marked'
          /\ pc' = "step"
  \/ /\ pc = "step"
     /\ Frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [] [Next]_vars

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

\*--------------------------------------------------------------------
\* Algorithm invariants
\*--------------------------------------------------------------------
\* Inv1: successor closure – every marked node's successors are also marked
Inv1 == \A n \in Marked : Succ[n] \subseteq Marked

\* Inv2: frontier consists of nodes that are reachable but not yet marked
Inv2 == Frontier = (Reachable \ Marked)

\* Inv3: when the algorithm terminates, the marked set equals the reachable set
Inv3 == (pc = "done") => (Marked = Reachable)

\*--------------------------------------------------------------------
\* Partial correctness property (same as Inv3, expressed as an invariant)
\*--------------------------------------------------------------------
PartialCorrectness == Inv3

\*--------------------------------------------------------------------
\* Liveness property: eventual termination
\*--------------------------------------------------------------------
Termination == <> (pc = "done")

\*--------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\*--------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES  == Termination

====