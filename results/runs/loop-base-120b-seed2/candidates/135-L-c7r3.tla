---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------
  Graph definition: each node has exactly two successors.
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      LET m == Cardinality(Nodes) IN
        { (n \mod m) + 1 , ((n + 1) \mod m) + 1 } ]

(*--------------------------------------------------------------------
  Bounded sequence operator used to replace the infinite Seq.
--------------------------------------------------------------------*)
MaxLen == Cardinality(Nodes)

LimitedSeq(S) == UNION { n \in 0..MaxLen : [1..n -> S] }

(*--------------------------------------------------------------------
  Variables of the sequential reachability algorithm.
--------------------------------------------------------------------*)
VARIABLES Marked, Frontier, pc

(*--------------------------------------------------------------------
  Initial state.
--------------------------------------------------------------------*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "run"

(*--------------------------------------------------------------------
  One step of the algorithm: expand a node from the frontier
  or stay in the terminal state.
--------------------------------------------------------------------*)
Expand ==
  /\ pc = "run"
  /\ \E n \in Frontier :
        LET succs == ConnectedToSomeButNotAll[n] IN
        /\ Marked'   = Marked \cup succs
        /\ Frontier' = (Frontier \cup succs) \ Marked
        /\ pc'       = IF Frontier' = {} THEN "done" ELSE "run"

Done ==
  /\ pc = "done"
  /\ UNCHANGED <<Marked, Frontier, pc>>

Next == Expand \/ Done

(*--------------------------------------------------------------------
  Specification.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(*--------------------------------------------------------------------
  Invariants.
--------------------------------------------------------------------*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == \A n \in Marked : ConnectedToSomeButNotAll[n] \subseteq Marked

Inv2 == Frontier \subseteq Nodes \ Marked

Inv3 == Marked = {Root} \cup UNION { ConnectedToSomeButNotAll[n] : n \in Marked }

PartialCorrectness ==
  /\ pc = "done"
  => Marked = Nodes

(*--------------------------------------------------------------------
  Liveness property: the algorithm eventually terminates.
--------------------------------------------------------------------*)
Termination == <> (pc = "done")
====