---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

(* ----------------------------------------------------------------------
   Succ is overridden by the configuration with ConnectedToSomeButNotAll.
   We provide a concrete definition here; the .cfg will replace all
   occurrences of Succ with ConnectedToSomeButNotAll.
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  [] n = 2 -> {1, 4}
  [] n = 3 -> {1, 4}
  [] n = 4 -> {2, 3}
  [] OTHER -> {}

(* ----------------------------------------------------------------------
   LimitedSeq replaces the unbounded Seq operator from the Sequences
   module.  It returns only those sequences whose length does not exceed
   the number of nodes, ensuring a finite state space.
   ---------------------------------------------------------------------- *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ----------------------------------------------------------------------
   Reachable nodes from Root via paths of bounded length.
   After substitution, Seq becomes LimitedSeq, making the quantifier
   range finite.
   ---------------------------------------------------------------------- *)
Reachable ==
  { t \in Nodes :
      \E s \in Seq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = t
        /\ \A i \in 1..(Len(s) - 1) :
            s[i+1] \in Succ[s[i]]
  }

(* ----------------------------------------------------------------------
   Initialization of the sequential reachability algorithm.
   ---------------------------------------------------------------------- *)
Init ==
  /\ Marked   = {Root}
  /\ Frontier = {Root}
  /\ pc       = "run"

(* ----------------------------------------------------------------------
   One step of the algorithm: expand the frontier using successors.
   ---------------------------------------------------------------------- *)
Step ==
  /\ pc = "run"
  LET new == ( UNION { Succ[n] : n \in Frontier } ) \ Marked IN
    /\ Marked'   = Marked \cup new
    /\ Frontier' = new
    /\ pc'       = IF new = {} THEN "done" ELSE "run"

Done ==
  /\ pc = "done"
  /\ UNCHANGED <<Marked, Frontier, pc>>

Next == Step \/ Done

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == \A n \in Marked : Succ[n] \subseteq (Marked \cup Frontier)

Inv2 == (Frontier = {}) => (pc = "done")

Inv3 == \A n \in Frontier : n \notin Marked

PartialCorrectness ==
  (pc = "done") => (Marked = Reachable)

(* ----------------------------------------------------------------------
   Liveness property: the algorithm eventually terminates.
   ---------------------------------------------------------------------- *)
Termination == <> (pc = "done")

====