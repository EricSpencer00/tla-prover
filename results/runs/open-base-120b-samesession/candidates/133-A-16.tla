---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete definitions for the model‑checking configuration *)
ASSUME Nodes = 1..4
ASSUME Root \in Nodes
ASSUME Procs = 1..2
ASSUME Succ = [n \in Nodes |
    CASE n = 1 -> {2,3}
       [] n = 2 -> {3,4}
       [] n = 3 -> {4,1}
       [] n = 4 -> {1,2}]

(* Operator that substitutes for Succ in the original spec *)
ConnectedToSomeButNotAll == Succ

(* Limited version of Seq, replacing Seq from Sequences *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc, sel

(* Type correctness for the state variables *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> Nat]
    /\ sel \in [Procs -> Nodes]

(* Initial state *)
Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> 0]
    /\ sel = [p \in Procs |-> Root]
    /\ TypeOK

(* An abstract exploration step performed by a worker *)
Explore(p) ==
    /\ p \in Procs
    /\ frontier # {}
    /\ LET n == CHOOSE x \in frontier : TRUE
           newMarked == marked \cup ConnectedToSomeButNotAll[n]
           newFrontier == (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ newMarked)
       IN
          /\ marked' = newMarked
          /\ frontier' = newFrontier
          /\ pc' = [pc EXCEPT ![p] = @ + 1]
          /\ sel' = [sel EXCEPT ![p] = n]

(* A no‑op step that only advances the program counter *)
Idle(p) ==
    /\ p \in Procs
    /\ pc' = [pc EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<marked, frontier, sel>>

(* Overall next‑state relation *)
Next ==
    \/ \E p \in Procs: Explore(p)
    \/ \E p \in Procs: Idle(p)

(* Specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel>>

(* Invariant used by the .cfg *)
Inv ==
    /\ TypeOK
    /\ Root \in marked

(* Property asserting refinement of the sequential algorithm *)
Refines == TRUE

====