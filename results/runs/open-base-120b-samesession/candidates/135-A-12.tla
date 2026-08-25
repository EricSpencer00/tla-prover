---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Concrete graph: each of the 4 nodes has exactly two successors.
  The operator ConnectedToSomeButNotAll is used (via the .cfg) in place
  of the abstract Succ relation.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
    [n \in Nodes |-> 
        CASE n = 1 -> {2,3}
         [] n = 2 -> {1,4}
         [] n = 3 -> {1,4}
         [] n = 4 -> {2,3}
         [] OTHER -> {}]

(*-----------------------------------------------------------------
  Bounded sequence operator: only sequences whose length does not
  exceed the number of nodes are allowed.
-----------------------------------------------------------------*)
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Reachable set defined via bounded sequences.
-----------------------------------------------------------------*)
ReachableFromRoot ==
    { n \in Nodes :
        \E p \in LimitedSeq(Nodes) :
            /\ Len(p) >= 1
            /\ p[1] = Root
            /\ p[Len(p)] = n
            /\ \A i \in 1..Len(p)-1 :
                 p[i+1] \in ConnectedToSomeButNotAll[p[i]] }

(*-----------------------------------------------------------------
  Initial state: start with only the root in the frontier.
-----------------------------------------------------------------*)
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "init"

(*-----------------------------------------------------------------
  One step of the sequential reachability algorithm.
-----------------------------------------------------------------*)
Next ==
    \/ /\ pc = "init"
       /\ \E n \in Frontier :
            /\ Marked' = Marked \cup {n}
            /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ Marked)
            /\ pc' = "step"
    \/ /\ pc = "step"
       /\ /\ Frontier = {}
       /\ Marked' = Marked
       /\ Frontier' = {}
       /\ pc' = "done"

Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Type correctness invariant.
-----------------------------------------------------------------*)
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"init", "step", "done"}

(*-----------------------------------------------------------------
  Invariant 1: successor closure – all successors of marked nodes are
  either already marked or lie in the frontier.
-----------------------------------------------------------------*)
Inv1 ==
    \A n \in Marked :
        ConnectedToSomeButNotAll[n] \subseteq Marked \cup Frontier

(*-----------------------------------------------------------------
  Invariant 2: decomposition – the root is always in the explored
  portion of the graph.
-----------------------------------------------------------------*)
Inv2 ==
    Root \in Marked \cup Frontier

(*-----------------------------------------------------------------
  Invariant 3: the set of marked nodes equals the set of nodes
  reachable from the root via bounded paths.
-----------------------------------------------------------------*)
Inv3 ==
    Marked = ReachableFromRoot

(*-----------------------------------------------------------------
  Partial correctness: when the algorithm terminates, the marked set
  equals the reachable set.
-----------------------------------------------------------------*)
PartialCorrectness ==
    (pc = "done") => (Marked = ReachableFromRoot)

(*-----------------------------------------------------------------
  Liveness property: eventual termination.
-----------------------------------------------------------------*)
Termination == <> (pc = "done")
================================================================================