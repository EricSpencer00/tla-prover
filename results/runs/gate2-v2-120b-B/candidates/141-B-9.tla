---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* The set of nodes reachable from Root. *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(* Initialization of variables. *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* Action a implements Misra's variant of the BFS algorithm. *)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE /\ \E v \in vroot :
                 IF v \notin marked
                    THEN /\ marked' = marked \cup {v}
                         /\ vroot' = vroot \cup Succ[v]
                         /\ pc' = "a"
                    ELSE /\ vroot' = vroot \ {v}
                         /\ marked' = marked
                         /\ pc' = "a"
               /\ UNCHANGED << >>

(* Allow stuttering after termination. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(a)

Termination == <> (pc = "Done")

(* Type correctness invariant. *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* Inductive invariant linking marked and successors. *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* Reachability invariant. *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(* Convenience invariant relating marked, vroot, and Reachable. *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* Partial correctness theorem: upon termination, marked equals Reachable. *)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

====