---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------
  Concrete successor relation: each node has exactly two successors.
  This operator replaces the abstract Succ after cfg substitution.
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE 
        n = "n1" -> {"n2","n3"}
        [] n = "n2" -> {"n3","n4"}
        [] n = "n3" -> {"n1","n4"}
        [] n = "n4" -> {"n1","n2"}
        [] OTHER -> {}
    ]

(*--------------------------------------------------------------------
  Bounded sequence operator that replaces the infinite Seq from the
  Sequences module.  Only sequences of length ≤ |Nodes| are allowed.
--------------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------
  State variables inherited from the sequential reachability algorithm.
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Initial state: only the root is in the frontier, nothing is marked.
--------------------------------------------------------------------*)
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = "Run"

(*--------------------------------------------------------------------
  Next-state relation (as in the sequential algorithm).
--------------------------------------------------------------------*)
Next ==
  \/ /\ pc = "Run"
     /\ frontier # {}
     /\ LET n == CHOOSE x \in frontier : TRUE IN
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked)
          /\ pc'       = "Run"
  \/ /\ pc = "Run"
     /\ frontier = {}
     /\ pc'       = "Done"
     /\ UNCHANGED <<marked, frontier>>

(*--------------------------------------------------------------------
  Full specification.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Invariants required by the cfg.
--------------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 ==
  \A n \in marked :
    ConnectedToSomeButNotAll[n] \subseteq Nodes

Inv2 ==
  \A n \in Nodes :
    (n \in marked) \/ (n \notin marked /\ n \notin frontier)

Inv3 ==
  marked = {
            n \in Nodes :
              \E p \in LimitedSeq(Nodes) :
                /\ Len(p) > 0
                /\ p[1] = Root
                /\ p[Len(p)] = n
                /\ \A i \in 1..(Len(p)-1) :
                     p[i+1] \in ConnectedToSomeButNotAll[p[i]]
           }

PartialCorrectness ==
  pc = "Done" =>
    marked = {
              n \in Nodes :
                \E p \in LimitedSeq(Nodes) :
                  /\ Len(p) > 0
                  /\ p[1] = Root
                  /\ p[Len(p)] = n
                  /\ \A i \in 1..(Len(p)-1) :
                       p[i+1] \in ConnectedToSomeButNotAll[p[i]]
             }

(*--------------------------------------------------------------------
  Liveness property: the algorithm eventually terminates.
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")
====