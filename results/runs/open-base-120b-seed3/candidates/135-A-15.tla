---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(*-------------------------------------------------------------------*)
(* Concrete graph: each node has exactly two successors               *)
(*-------------------------------------------------------------------*)
Edge == {
    <<1, 2>>, <<1, 3>>,
    <<2, 3>>, <<2, 4>>,
    <<3, 1>>, <<3, 4>>,
    <<4, 1>>, <<4, 2>>
}

(* Operator that will replace the Succ constant in the configuration *)
ConnectedToSomeButNotAll(n) == { m \in Nodes : <<n, m>> \in Edge }

(*-------------------------------------------------------------------*)
(* Bounded sequence operator for model checking                       *)
(*-------------------------------------------------------------------*)
MaxLen == Cardinality(Nodes)

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

(*-------------------------------------------------------------------*)
(* Reachable set definition using the (overridden) Succ operator      *)
(*-------------------------------------------------------------------*)
Reachable ==
    { n \in Nodes :
        \E s \in LimitedSeq(Nodes) :
            /\ Len(s) > 0
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
    }

(*-------------------------------------------------------------------*)
(* State variables                                                  *)
(*-------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-------------------------------------------------------------------*)
(* Initial state                                                    *)
(*-------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = 0

(*-------------------------------------------------------------------*)
(* Next-state relation                                              *)
(*-------------------------------------------------------------------*)
Next ==
    \/ /\ frontier = {}
       /\ UNCHANGED <<marked, frontier, pc>>
    \/ /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ (marked \cup {n}))
            /\ pc'       = pc + 1
            /\ UNCHANGED << >>

(*-------------------------------------------------------------------*)
(* Specification                                                    *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-------------------------------------------------------------------*)
(* Invariants                                                       *)
(*-------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in Nat

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    /\ Root \in marked \cup frontier
    /\ \A n \in marked \cup frontier :
          (n = Root) \/ (\E m \in marked \cup frontier : n \in Succ[m])

Inv3 ==
    marked = Reachable

PartialCorrectness ==
    (frontier = {} => marked = Reachable)

(*-------------------------------------------------------------------*)
(* Liveness property                                                *)
(*-------------------------------------------------------------------*)
Termination == <> (frontier = {})

====