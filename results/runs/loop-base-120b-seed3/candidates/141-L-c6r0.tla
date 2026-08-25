---- MODULE Reachable ----
EXTENDS Sequences

CONSTANTS Nodes, Root, Succ

\*--- Operators replacing left‑hand names in the .cfg ---------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == 
  { <<>> } \cup { <<x>> : x \in S }

\*--- Derived relations -------------------------------------------------------------
SuccRel == { <<n, m>> : n \in Nodes /\ m \in ConnectedToSomeButNotAll[n] }

ReachableFromSet(S) == 
  { y \in Nodes : \E x \in S : <<x, y>> \in SuccRel^* }

\*--- Variables ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\*--- Initial state -----------------------------------------------------------------
Init == 
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "run"

\*--- Next-state relation ------------------------------------------------------------
Next == 
  \/ \E n \in Frontier :
        /\ n \notin Marked
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = Frontier \cup ConnectedToSomeButNotAll[n]
        /\ pc' = pc
  \/ \E n \in Frontier :
        /\ n \in Marked
        /\ Marked' = Marked
        /\ Frontier' = Frontier \ {n}
        /\ pc' = pc
  \/ /\ Frontier = {}
     /\ pc = "run"
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>

\*--- Specification -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\*--- Invariants --------------------------------------------------------------------
TypeOK == 
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == 
  \A n \in Marked : ConnectedToSomeButNotAll[n] \subseteq Marked \cup Frontier

Inv2 == 
  Marked \cup ReachableFromSet(Frontier) = ReachableFromSet(Marked \cup Frontier)

Inv3 == 
  ReachableFromSet({Root}) = Marked \cup ReachableFromSet(Frontier)

PartialCorrectness == 
  (pc = "done") => (Marked = ReachableFromSet({Root}))

\*--- Liveness property -------------------------------------------------------------
Termination == <> (Frontier = {})

\*--- Exported identifiers -----------------------------------------------------------
\* (the .cfg file expects these exact names)
\* Specification
\* Invariants
\* Property
====