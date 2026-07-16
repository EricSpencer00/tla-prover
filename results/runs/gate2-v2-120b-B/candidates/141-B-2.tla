---- MODULE Reachable ----
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  The   *)
(* algorithm is due to Jayadev Misra.  It is, to my knowledge, a new       *)
(* variant of a fairly obvious breadth-first search for reachable nodes.   *)
(* The rest of the comment section is unchanged from the original module. *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.  The   *)
(* purpose of the algorithm is to compute Reachable.                        *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ vroot = {Root}
  /\ pc = "a"

\* ----------------------------------------------------------------------
\* Action a (the main loop)
\* ----------------------------------------------------------------------
a ==
  /\ pc = "a"
  /\ IF vroot /= {}
       THEN
         /\ \E v \in vroot :
              IF v \notin marked
                 THEN /\ marked' = marked \cup {v}
                      /\ vroot'  = vroot  \cup Succ[v]
                 ELSE /\ marked' = marked
                      /\ vroot'  = vroot \ {v}
         /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << marked, vroot >>

\* ----------------------------------------------------------------------
\* Allow infinite stuttering after termination
\* ----------------------------------------------------------------------
Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ a
  \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(a)   \* weak fairness of the main loop

Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ vroot  \in SUBSET Nodes
  /\ pc \in {"a", "Done"}
  /\ (pc = "Done") => (vroot = {})

Inv1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
  (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 ==
  Reachable = marked \cup ReachableFrom(vroot)

\* ----------------------------------------------------------------------
\* Partial correctness theorem
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

\* ----------------------------------------------------------------------
\* Liveness (termination) theorem, assuming Reachable is finite
\* ----------------------------------------------------------------------
THEOREM ASSUME IsFiniteSet(Reachable)
         PROVE Spec => <> (pc = "Done")
====