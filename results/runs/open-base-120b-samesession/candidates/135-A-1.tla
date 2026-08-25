---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* successor relation used by the algorithm; this operator is substituted for Succ in the cfg *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* a finite version of Seq, limited by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* concrete assumptions to make the model finite *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root \in Nodes
ASSUME Succ \in [Nodes -> SUBSET Nodes]
ASSUME \A n \in Nodes : Cardinality(Succ[n]) = 2

(* ----------------------------------------------------------------------
   Initial state (as in the sequential reachability algorithm)
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(* ----------------------------------------------------------------------
   Next action (placeholder – the real algorithm actions are inherited)
   ---------------------------------------------------------------------- *)
Next ==
    \/ /\ pc = "Init"
       /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ marked)
       /\ pc' = "Run"
    \/ /\ pc = "Run"
       /\ IF frontier = {} THEN pc' = "Done" ELSE pc' = "Run"
       /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Run", "Done"}

Inv1 == 
    (* successor‑closure: every marked node is reachable from Root via a bounded path *)
    \A n \in marked :
        \E p \in LimitedSeq(Nodes) :
            /\ Len(p) > 0
            /\ p[1] = Root
            /\ p[Len(p)] = n
            /\ \A i \in 1..(Len(p)-1) :
                 p[i+1] \in ConnectedToSomeButNotAll(p[i])

Inv2 ==
    (* reachability decomposition: frontier are exactly those marked nodes
       that still have an unmarked successor *)
    frontier = { n \in marked :
                  \E m \in ConnectedToSomeButNotAll(n) : m \notin marked }

Inv3 ==
    (* reachable‑set equality: marked equals the set of nodes reachable from Root *)
    marked = { n \in Nodes :
                \E p \in LimitedSeq(Nodes) :
                    /\ Len(p) > 0
                    /\ p[1] = Root
                    /\ p[Len(p)] = n
                    /\ \A i \in 1..(Len(p)-1) :
                         p[i+1] \in ConnectedToSomeButNotAll(p[i]) }

PartialCorrectness ==
    /\ (frontier = {} => pc = "Done")
    /\ (pc = "Done" => marked = { n \in Nodes :
                                   \E p \in LimitedSeq(Nodes) :
                                       /\ Len(p) > 0
                                       /\ p[1] = Root
                                       /\ p[Len(p)] = n
                                       /\ \A i \in 1..(Len(p)-1) :
                                            p[i+1] \in ConnectedToSomeButNotAll(p[i]) })

(* ----------------------------------------------------------------------
   Liveness property
   ---------------------------------------------------------------------- *)

Termination == <> (pc = "Done")
=============================================================================