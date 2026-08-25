---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(*-----------------------------------------------------------------
  Configuration operator that will replace Succ via the .cfg file.
  It provides, for each node, exactly two distinct successors chosen
  nondeterministically from the other nodes.  This definition avoids
  arithmetic on node values, making it work for arbitrary (non‑numeric)
  node identifiers.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      LET others == Nodes \ {n} IN
        IF Cardinality(others) >= 2 THEN
          LET x == CHOOSE a \in others : TRUE IN
            { x, CHOOSE b \in others \ {x} : TRUE }
        ELSE others
   ]

(*-----------------------------------------------------------------
  Finite version of Seq for model checking.
-----------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Variables of the sequential Misra reachability algorithm.
-----------------------------------------------------------------*)
VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Helper: set of nodes reachable from Root via a bounded path.
-----------------------------------------------------------------*)
Path(s) ==
  /\ Len(s) >= 1
  /\ s[1] = Root
  /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in Succ[s[i]]

ReachableSet ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Path(s)
        /\ s[Len(s)] = n }

(*-----------------------------------------------------------------
  Initialization.
-----------------------------------------------------------------*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "run"

(*-----------------------------------------------------------------
  Next-state relation.
-----------------------------------------------------------------*)
Next ==
  \/ /\ pc = "run"
     /\ Frontier # {}
     /\ \E n \in Frontier :
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked)
          /\ pc' = IF Frontier' = {} THEN "done" ELSE "run"
  \/ /\ pc = "done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Specification.
-----------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Invariants.
-----------------------------------------------------------------*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == \A n \in Marked : Succ[n] \subseteq Marked \cup Frontier

Inv2 == Marked \cup Frontier = ReachableSet

Inv3 == Marked = ReachableSet

PartialCorrectness == (pc = "done") => Marked = ReachableSet

(*-----------------------------------------------------------------
  Liveness property: termination.
-----------------------------------------------------------------*)
Termination == <> (pc = "done")

=============================================================================