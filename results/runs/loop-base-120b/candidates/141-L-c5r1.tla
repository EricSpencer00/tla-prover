---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Reachability from a set of nodes using finite sequences *)
Reach(S) == 
  { n \in Nodes :
      \E p \in LimitedSeq(Nodes) :
        /\ Len(p) >= 1
        /\ p[1] \in S
        /\ p[Len(p)] = n
        /\ \A i \in 1..Len(p)-1 : p[i+1] \in Succ[p[i]]
  }

VARIABLES marked, frontier, pc

Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

Action == 
  /\ pc = "Run"
  /\ frontier # {}
  /\ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked'   = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
           /\ marked'   = marked
           /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Terminate == 
  /\ pc = "Run"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next == Action \/ Terminate \/ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Invariants *)
TypeOK == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ Root \in Nodes
  /\ pc \in {"Run", "Done"}

Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == Reach(marked \cup frontier) = marked \cup Reach(frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == (pc = "Done") => marked = Reach({Root})

(* Liveness property *)
Termination == <> (pc = "Done")
====