---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* Set of nodes reachable from Root *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

(* Helper tuple of all variables *)
vars == << marked, vroot, pc >>

(* Initial state *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* Action a as described in the PlusCal code.
   We give an explicit definition that ensures every variable is assigned. *)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE (* vroot is non‑empty *)
               /\ \E v \in vroot :
                     /\ IF v \notin marked
                           THEN /\ marked' = marked \cup {v}
                                /\ vroot' = vroot \cup Succ[v]
                           ELSE /\ marked' = marked
                                /\ vroot' = vroot \ {v}
                     /\ pc' = "a"

(* Allow infinite stuttering once termination is reached. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

(* Full specification *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

Termination == <> (pc = "Done")

(* Type correctness invariant *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* Invariant relating successors of marked nodes *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* Reachability invariant *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(* Convenience invariant linking marked and Reachable *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* Partial correctness theorem: when terminated, marked = Reachable *)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

=============================================================================