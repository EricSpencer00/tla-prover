---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

(*-----------------------------------------------------------------
  Concrete graph: each node has exactly two successors.
  This operator substitutes for the abstract Succ.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> {
      ((n) % Cardinality(Nodes)) + 1,
      ((n + 1) % Cardinality(Nodes)) + 1
   }]

(*-----------------------------------------------------------------
  Bounded sequence operator used to make the model finite.
-----------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ pc = "init"
  /\ Marked = {}
  /\ Frontier = {Root}

(*-----------------------------------------------------------------
  Helper: reachable nodes via a bounded path
-----------------------------------------------------------------*)
Reachable(n) ==
  \E s \in LimitedSeq(Nodes) :
    /\ Len(s) > 0
    /\ Head(s) = Root
    /\ Last(s) = n
    /\ \A i \in 1..Len(s)-1 :
         s[i+1] \in ConnectedToSomeButNotAll[s[i]]

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
  \/ /\ pc = "init"
     /\ pc' = "step"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "step"
     /\ LET new == UNION { ConnectedToSomeButNotAll[n] : n \in Frontier } IN
        /\ Marked' = Marked \cup Frontier
        /\ Frontier' = new \ Marked'
        /\ pc' = IF Frontier' = {} THEN "done" ELSE "step"
        /\ UNCHANGED <<>>
  \/ /\ pc = "done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

Inv1 == \A n \in Marked :
          ConnectedToSomeButNotAll[n] \subseteq Marked \cup Frontier

Inv2 == \A n \in Frontier : Reachable(n)

Inv3 == Marked \subseteq { n \in Nodes : Reachable(n) }

PartialCorrectness == (pc = "done") => 
                        Marked = { n \in Nodes : Reachable(n) }

(*-----------------------------------------------------------------
  Liveness property: termination
-----------------------------------------------------------------*)
Termination == <> (pc = "done")

====