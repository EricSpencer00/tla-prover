---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Operator that will substitute for Succ (bounded successor relation)
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  []   n = 2 -> {3, 4}
  []   n = 3 -> {1, 4}
  []   n = 4 -> {1, 2}
  []   TRUE  -> {}

\* ----------------------------------------------------------------------
\* Limited version of the sequence operator (finite sequences only)
\* ----------------------------------------------------------------------
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables of the sequential reachability algorithm
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Helper definition of the set of nodes reachable from Root via
\* a bounded sequence of successors
\* ----------------------------------------------------------------------
ReachableSet ==
  { n \in Nodes :
      \E s \in LimitedSeq :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1 .. Len(s)-1 :
            s[i+1] \in Succ[s[i]]
  }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Marked   = {Root}
  /\ Frontier = {Root}
  /\ pc       = "run"

\* ----------------------------------------------------------------------
\* Transition that processes a node from the frontier
\* ----------------------------------------------------------------------
ProcessNode ==
  /\ Frontier # {}
  /\ \E n \in Frontier :
       LET new == Succ[n] \ Marked IN
         /\ Marked'   = Marked \cup new
         /\ Frontier' = (Frontier \ {n}) \cup new
         /\ pc'       = pc

\* ----------------------------------------------------------------------
\* Transition that records termination when the frontier is empty
\* ----------------------------------------------------------------------
Terminate ==
  /\ Frontier = {}
  /\ Marked'   = Marked
  /\ Frontier' = Frontier
  /\ pc'       = "done"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ ProcessNode
        \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Invariant 1: Successor closure
\* ----------------------------------------------------------------------
Inv1 ==
  \A n \in Marked : Succ[n] \subseteq Marked \cup Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: All marked nodes are reachable from the root
\* ----------------------------------------------------------------------
Inv2 ==
  Marked \subseteq ReachableSet

\* ----------------------------------------------------------------------
\* Invariant 3: Reachable set equals marked ∪ frontier
\* ----------------------------------------------------------------------
Inv3 ==
  ReachableSet = Marked \cup Frontier

\* ----------------------------------------------------------------------
\* Partial correctness: when finished, frontier empty and marked set
\* equals the reachable set
\* ----------------------------------------------------------------------
PartialCorrectness ==
  /\ pc = "done"
  /\ Frontier = {}
  /\ Marked = ReachableSet

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

====