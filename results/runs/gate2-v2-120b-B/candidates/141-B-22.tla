---- MODULE Reachable ----
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  The   *)
(* algorithm is due to Jayadev Misra.  It is, to my knowledge, a new       *)
(* variant of a fairly obvious breadth‑first search for reachable nodes.   *)
(* The module describes the algorithm and its invariants.                  *)
(***************************************************************************)

EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.        *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

(***************************************************************************)
(* Variables of the algorithm.                                            *)
(***************************************************************************)
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(***************************************************************************)
(* Initialization.                                                       *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc    = "a"

(***************************************************************************)
(* Action a implements Misra's variant of the breadth‑first search.      *)
(* The action must always assign a value to every variable that appears   *)
(* in the global state vector (marked, vroot, pc).  In the original         *)
(* specification the assignment to pc was missing in the branch that      *)
(* adds a new node to marked, which caused TLC to report an incompletely *)
(* specified successor state.  The missing assignment is repaired by      *)
(* explicitly setting pc to "a" in that branch.                           *)
(***************************************************************************)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE 
               LET v == CHOOSE x \in vroot : TRUE
               IN
               IF v \notin marked
                  THEN /\ marked' = marked \cup {v}
                       /\ vroot'  = vroot \cup Succ[v]
                       /\ pc'     = "a"
                  ELSE /\ marked' = marked
                       /\ vroot'  = vroot \ {v}
                       /\ pc'     = "a"

(***************************************************************************)
(* Allow infinite stuttering after termination to avoid deadlock.         *)
(***************************************************************************)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ a
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

Termination ==
    <> (pc = "Done")

(***************************************************************************)
(* Type correctness invariant.                                            *)
(***************************************************************************)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(***************************************************************************)
(* Invariant Inv1: each node's successors are already discovered or in    *)
(* the frontier.                                                          *)
(***************************************************************************)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(***************************************************************************)
(* Invariant Inv2: relationship between marked, vroot and ReachableFrom. *)
(***************************************************************************)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(***************************************************************************)
(* Invariant Inv3: the algorithm maintains the equality with the         *)
(* specification of Reachable.                                            *)
(***************************************************************************)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(***************************************************************************)
(* Partial correctness theorem (stated as an invariant).                 *)
(***************************************************************************)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

=============================================================================