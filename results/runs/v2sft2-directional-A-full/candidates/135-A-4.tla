---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

(*--algorithm definitions--*)

VARIABLES marked, frontier, pc

(* Constants required by the .cfg *)
CONSTANTS Nodes, Root, Succ, Seq

(* Derived constant for the number of nodes *)
NodesCount == Cardinality(Nodes)

(* ------------------------------------------------------------------------ *)
(* Type correctness invariant *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Start", "Mark", "Forward", "Done"}
    /\ \A n \in Nodes : (n \in marked) \/ (n \in frontier)

(* ------------------------------------------------------------------------ *)
(* Helper: the set of nodes that are successors of the current frontier *)
NextSet ==
    \E n \in frontier : Succ[n] \subseteq marked

(* ------------------------------------------------------------------------ *)
(* Invariant 1: Successor closure (the marked set is closed under Succ) *)
Inv1 == \A n \in marked : Succ[n] \subseteq marked

(* ------------------------------------------------------------------------ *)
(* Invariant 2: Reachability decomposition *)
Inv2 == marked = {Root} \cup { n \in Nodes : \E m \in marked : n \in Succ[m] }

(* ------------------------------------------------------------------------ *)
(* Invariant 3: Reachable set equality (with bounded sequence) *)
Inv3 ==
    \A n \in Nodes :
        (n \in marked) \iff (\E s \in Seq : s[1] = Root /\ Last(s) = n /\ \A i \in 1..Len(s)-1 : s[i] \in Succ[s[i+1]])

(* ------------------------------------------------------------------------ *)
(* Partial correctness property *)
PartialCorrectness ==
    /\ Inv1
    /\ Inv2
    /\ Inv3

(* ------------------------------------------------------------------------ *)
(* Initialization (exactly as in the sequential algorithm) *)
Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "Mark"

(* ------------------------------------------------------------------------ *)
(* Actions *)

Mark ==
    /\ pc = "Mark"
    /\ \E n \in frontier : n \notin marked
    /\ LET n == CHOOSE n \in frontier : n \notin marked IN
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \ Succ[n]
        /\ pc' = IF frontier' = {} THEN "Done" ELSE "Mark"

(* ------------------------------------------------------------------------ *)
Next ==
    Mark

(* ------------------------------------------------------------------------ *)
(* Specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ------------------------------------------------------------------------ *)
(* Temporal property: termination *)
Termination ==
    [] (pc = "Done")

====