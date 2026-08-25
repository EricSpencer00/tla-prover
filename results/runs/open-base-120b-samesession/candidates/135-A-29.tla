---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Operators required by the configuration
 -----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Reachability definition using the bounded sequence operator
 -----------------------------------------------------------------*)
Reach == 
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..(Len(s)-1) :
            s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  }

(*-----------------------------------------------------------------
  Algorithm state and actions (inherited from the sequential spec)
 -----------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

Next ==
  \/ /\ pc = "run"
     /\ frontier # {}
     /\ LET n == CHOOSE x \in frontier : TRUE IN
        /\ marked'   = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked')
        /\ pc'       = "run"
  \/ /\ pc = "run"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants required by the .cfg file
 -----------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == frontier \subseteq UNION { ConnectedToSomeButNotAll[n] : n \in marked }

Inv2 == marked \subseteq Reach

Inv3 == (pc = "done") => (marked = Reach)

PartialCorrectness == Inv3

(*-----------------------------------------------------------------
  Liveness property
 -----------------------------------------------------------------*)
Termination == <> (pc = "done")

====