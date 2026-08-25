---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(* Succ will be overridden by ConnectedToSomeButNotAll in the .cfg file *)
Succ == [n \in Nodes |-> {}]

ConnectedToSomeButNotAll(n) == Succ[n]

VARIABLES marked, frontier, pc

(* Relation derived from the successor function, used for reachability *)
SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

(* Nodes reachable from a set S (zero or more steps) *)
Reach(S) == 
    S \cup { n \in Nodes : \E m \in S : <<m, n>> \in TC(SuccRel) }

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

Next ==
    \/ /\ frontier # {}
       /\ \E n \in frontier :
          \/ /\ n \notin marked
             /\ marked'   = marked \cup {n}
             /\ frontier' = frontier \cup Succ[n]
             /\ UNCHANGED pc
          \/ /\ n \in marked
             /\ marked'   = marked
             /\ frontier' = frontier \ {n}
             /\ UNCHANGED pc
    \/ /\ frontier = {}
       /\ pc = "Run"
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

TypeOK == 
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes

Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == (frontier = {}) => marked = Reach({Root})

Termination == <> (frontier = {})

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

====