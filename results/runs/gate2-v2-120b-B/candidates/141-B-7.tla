---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* The set of nodes reachable from Root. *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(* Initial state *)
Init ==
  /\ marked = {}
  /\ vroot = {Root}
  /\ pc = "a"

(* Action a: the core step of Misra's algorithm, together with
   termination handling.  The variable pc is always assigned a value,
   either staying at "a" or moving to "Done". *)
a ==
  /\ pc = "a"
  /\ IF vroot = {}
       THEN /\ pc' = "Done"
            /\ UNCHANGED << marked, vroot >>
       ELSE /\ \E v \in vroot:
              IF v \notin marked
                 THEN /\ marked' = marked \cup {v}
                      /\ vroot'  = vroot  \cup Succ[v]
                 ELSE /\ marked' = marked
                      /\ vroot'  = vroot \ {v}
            /\ pc' = "a"

(* Allow infinite stuttering after termination to avoid deadlock. *)
Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == a \/ Terminating

(* Full specification with weak fairness on the core action. *)
Spec == Init /\ [][Next]_vars /\ WF_vars(a)

(* Invariant describing the algorithm's safety condition. *)
Inv ==
  /\ marked \in SUBSET Nodes
  /\ vroot  \in SUBSET Nodes
  /\ pc \in {"a", "Done"}
  /\ (pc = "Done") => (vroot = {})
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* Partial correctness property: when the algorithm terminates,
   marked equals the set of reachable nodes from Root. *)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

=============================================================================