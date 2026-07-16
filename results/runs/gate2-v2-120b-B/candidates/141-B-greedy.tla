---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* The set of nodes reachable from Root. *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

(* Convenience tuple of all variables. *)
vars == << marked, vroot, pc >>

(* Initial state. *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* Action a: the core step of the algorithm. *)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE /\ \E v \in vroot:
                 IF v \notin marked
                    THEN /\ marked' = marked \cup {v}
                         /\ vroot' = vroot \cup Succ[v]
                         /\ pc' = "a"
                    ELSE /\ marked' = marked
                         /\ vroot' = vroot \ {v}
                         /\ pc' = "a"

(* Allow stuttering after termination to avoid deadlock. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(a)

Termination == <> (pc = "Done")

(* Type correctness invariant. *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* Invariant used in the original proof. *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* Partial correctness theorem. *)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

====