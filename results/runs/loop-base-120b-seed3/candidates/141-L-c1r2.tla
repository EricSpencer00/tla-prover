---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  CONSTANTS
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ

(*-----------------------------------------------------------------
  Operator that the .cfg will substitute for Succ
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == 
  \* By default just return Succ[n]; the configuration may replace
  \* this definition with a bounded version.
  Succ[n]

(*-----------------------------------------------------------------
  Finite version of Seq (replaces Seq from Sequences)
-----------------------------------------------------------------*)
CONSTANT MaxSeqLen
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
SuccRel == { <<x, y>> : ( /\ x \in Nodes /\ y \in Succ[x] ) }

RECURSIVE Reachable(_)
Reachable(S) == 
  S \cup { n \in Nodes : 
            (\E m \in Reachable(S) : <<m, n>> \in SuccRel) }

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Step ==
  /\ pc = "Run"
  /\ \E n \in frontier :
        IF n \notin marked THEN
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
           /\ pc' = "Run"
        ELSE
           /\ marked' = marked
           /\ frontier' = frontier \ {n}
           /\ pc' = "Run"

Terminate ==
  /\ pc = "Run"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED marked

StutterDone ==
  /\ pc = "Done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == Step \/ Terminate \/ StutterDone

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == Reachable(marked \cup frontier) = marked \cup Reachable(frontier)

Inv3 == Reachable({Root}) = marked \cup Reachable(frontier)

PartialCorrectness == (frontier = {} => marked = Reachable({Root}))

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == <> (frontier = {})

(*-----------------------------------------------------------------
  The set of all invariants and properties required by the .cfg
-----------------------------------------------------------------*)
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES == Termination

====