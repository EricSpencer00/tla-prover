---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* Bounded sequence operator – used instead of the infinite Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Concrete successor relation – will replace Succ via the .cfg substitution *)
ConnectedToSomeButNotAll == 
    [n \in Nodes |-> 
        IF n = 1 THEN {2,3}
        ELSE IF n = 2 THEN {3,4}
        ELSE IF n = 3 THEN {4,1}
        ELSE {1,2}
    ]

(* Initial state *)
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "step"

(* One step of the reachability algorithm *)
Step ==
    /\ pc = "step"
    /\ \E n \in frontier :
        LET new == Succ[n] \ marked IN
            /\ marked'   = marked \cup new
            /\ frontier' = (frontier \ {n}) \cup new
            /\ pc'       = IF frontier' = {} THEN "done" ELSE "step"

(* Stutter when algorithm has finished *)
Done ==
    /\ pc = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Done

(* Full specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"step", "done"}

(* Successor‑closure invariant *)
Inv1 == \A n \in marked : Succ[n] \subseteq marked

(* Frontier is always a subset of the marked set *)
Inv2 == frontier \subseteq marked

(* Definition of the reachable set using bounded sequences *)
Reachable ==
    { n \in Nodes :
        \E s \in LimitedSeq(Nodes) :
            /\ Len(s) >= 1
            /\ Head(s) = Root
            /\ Last(s) = n
            /\ \A i \in 1..(Len(s)-1) :
                s[i+1] \in Succ[s[i]]
    }

(* Equality of the computed marked set with the true reachable set *)
Inv3 == (pc = "done") => (marked = Reachable)

(* Partial correctness property – same as Inv3, exposed as a separate invariant *)
PartialCorrectness == (pc = "done") => (marked = Reachable)

(* Liveness property: the algorithm eventually terminates *)
Termination == <> (pc = "done")

====