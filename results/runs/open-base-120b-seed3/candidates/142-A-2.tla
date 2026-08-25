---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Edge

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

TypeInv == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"init","run","done"}

Succ(n) == { m \in Nodes : <<n,m>> \in Edge }

EdgeStar == TC(Edge)

ReachableFrom(S) ==
    { n \in Nodes :
        \E s \in S : <<s,n>> \in EdgeStar }

(* ----------------------------------------------------------------------
   Invariants required by the proof
   ---------------------------------------------------------------------- *)

Inv1 == /\ TypeInv
        /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier

Inv2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(* ----------------------------------------------------------------------
   Algorithm skeleton (initial state and next-state relation)
   ---------------------------------------------------------------------- *)

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"
    /\ TypeInv

Next ==
    \/ /\ pc = "init"
       /\ pc' = "run"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "run"
       /\ (* placeholder for a real algorithm step;
            for the purpose of this specification we allow stuttering *)
       /\ UNCHANGED <<marked, frontier, pc>>
    \/ /\ pc = "run"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<\<marked, frontier, pc\>>

(* ----------------------------------------------------------------------
   Collections of properties for the model checker
   ---------------------------------------------------------------------- *)

INVARIANTS == <<Inv1, Inv2, Inv3>>
PROPERTIES == <<Inv1, Inv2, Inv3>>

====