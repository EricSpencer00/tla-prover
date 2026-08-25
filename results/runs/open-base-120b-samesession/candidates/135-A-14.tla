---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

(*-----------------------------------------------------------------
  Constants required by the configuration.
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ

(*-----------------------------------------------------------------
  Operator that provides a concrete finite successor relation.
  The .cfg file substitutes this operator for the constant Succ.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  LET nSucc1(n) == (n % Cardinality(Nodes)) + 1
      nSucc2(n) == ((n + 1) % Cardinality(Nodes)) + 1
  IN [n \in Nodes |-> { nSucc1(n), nSucc2(n) }]

(*-----------------------------------------------------------------
  Bounded version of Seq to keep the model finite.
  The .cfg file substitutes this operator for Seq.
-----------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  State variables (inherited from the sequential reachability algorithm)
-----------------------------------------------------------------*)
VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Initialization of the algorithm.
-----------------------------------------------------------------*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "init"

(*-----------------------------------------------------------------
  One step of the algorithm: expand the frontier.
-----------------------------------------------------------------*)
Step ==
  /\ pc = "step"
  /\ Let newFrontier == UNION { Succ[n] : n \in Frontier } IN
     /\ Marked'   = Marked \cup Frontier
     /\ Frontier' = newFrontier \ Marked'
  /\ IF Frontier' = {} THEN pc' = "done" ELSE pc' = "step"

(*-----------------------------------------------------------------
  Transition from init to the first step.
-----------------------------------------------------------------*)
Start ==
  /\ pc = "init"
  /\ pc' = "step"
  /\ UNCHANGED <<Marked, Frontier>>

(*-----------------------------------------------------------------
  Next-state relation.
-----------------------------------------------------------------*)
Next ==
  \/ Start
  \/ Step

(*-----------------------------------------------------------------
  Specification of the system.
-----------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Type correctness invariant.
-----------------------------------------------------------------*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

(*-----------------------------------------------------------------
  Invariant 1: successor closure.
-----------------------------------------------------------------*)
Inv1 ==
  \A n \in Marked : Succ[n] \subseteq Marked

(*-----------------------------------------------------------------
  Invariant 2: every marked node is reachable via a bounded path.
-----------------------------------------------------------------*)
Inv2 ==
  \A n \in Marked :
    \E p \in LimitedSeq(Nodes) :
      /\ Len(p) > 0
      /\ p[1] = Root
      /\ p[Len(p)] = n
      /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]]

(*-----------------------------------------------------------------
  Invariant 3: marked set equals the set of nodes reachable from Root.
-----------------------------------------------------------------*)
Inv3 ==
  \A n \in Nodes :
    (n \in Marked) \equiv
      \E p \in LimitedSeq(Nodes) :
        /\ Len(p) > 0
        /\ p[1] = Root
        /\ p[Len(p)] = n
        /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]]

(*-----------------------------------------------------------------
  Partial correctness: when the algorithm terminates, the marked set
  exactly matches the reachable nodes.
-----------------------------------------------------------------*)
PartialCorrectness ==
  pc = "done" => Inv3

(*-----------------------------------------------------------------
  Liveness property: the algorithm eventually terminates.
-----------------------------------------------------------------*)
Termination == <> (pc = "done")

====