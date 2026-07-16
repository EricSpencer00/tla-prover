---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(* Initial state *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* Action a: the core step of the algorithm *)
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
               /\ UNCHANGED pc

(* Allow infinite stuttering after termination *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(a)

Termination == <> (pc = "Done")

(* Type correctness invariant *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* Invariant ensuring successors of marked nodes stay within marked ∪ vroot *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* Reachability invariant relating marked and vroot *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(* Convenience invariant linking the algorithm's result to the specification *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* Partial correctness theorem: if the algorithm terminates, marked equals Reachable *)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

=============================================================================