---- MODULE ReachableProofs ----
EXTENDS SeqReachAlg, ReachabilityLemmas, Naturals, Sequences

CONSTANTS Nodes, Root, Edge

VARIABLES Marked, Frontier, pc

INIT == SeqReachAlg.INIT
NEXT == SeqReachAlg.NEXT

(* --- type correctness --- *)
TypeCorrect == 
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"start", "loop", "done"}

Succ(v) == Edge[v]

(* --- invariant 1: every successor of a marked node is marked or in frontier --- *)
Inv1 == 
  /\ TypeCorrect
  /\ \A v \in Marked : \A w \in Succ(v) : w \in Marked \/ Frontier

(* --- reachability helper (recursive definition) --- *)
RECURSIVE ReachableFrom(_)

ReachableFrom(S) == 
  IF S = {} THEN {} 
  ELSE S \cup ReachableFrom({ w \in Nodes : \E v \in S : w \in Edge[v] })

(* --- invariant 2 --- *)
Inv2 == 
  Marked \cup ReachableFrom(Frontier) = ReachableFrom(Marked \cup Frontier)

(* --- invariant 3 --- *)
Inv3 == 
  ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

INVARIANTS == /\ Inv1 /\ Inv2 /\ Inv3

(* --- partial‑correctness property (termination implies marked = reachable) --- *)
Property == [] ( ~Enabled(NEXT) => Marked = ReachableFrom({Root}) )

PROPERTIES == Property

Spec == INIT /\ [][NEXT]_<<Marked, Frontier, pc>>

====