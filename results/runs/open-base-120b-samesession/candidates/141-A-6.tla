---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Rel == [x \in Nodes, y \in Nodes |-> y \in Succ[x]]

Reach(S) ==
  S \cup { n \in Nodes : \E m \in S : <<m, n>> \in TC(Rel) }

ConnectedToSomeButNotAll(n) ==
  { m \in Nodes : m \in Succ[n] /\ m # n }

LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= 5 }

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Type correctness
--------------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Running", "Done"}

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"

(*--------------------------------------------------------------------
  Main algorithm action (chosen nondeterministically from frontier)
--------------------------------------------------------------------*)
MainAction ==
  \E n \in frontier :
    IF n \notin marked THEN
      /\ marked' = marked \cup {n}
      /\ frontier' = frontier \cup Succ[n]
    ELSE
      /\ marked' = marked
      /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "Done" ELSE "Running"

(*--------------------------------------------------------------------
  Next relation (includes stuttering when done)
--------------------------------------------------------------------*)
Next ==
  \/ /\ pc = "Running"
     /\ MainAction
  \/ /\ pc = "Done"
     /\ UNCHANGED <<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(MainAction)

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
Inv1 ==
  \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
  marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
  Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
  pc = "Done" => marked = Reach({Root})

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

====