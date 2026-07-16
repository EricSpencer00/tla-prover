---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* The set of nodes reachable from Root, as defined in Reachability *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

(* Tuple of all variables, used for stuttering and fairness *)
vars == << marked, vroot, pc >>

(* Initial state *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* One iteration of the algorithm *)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE
               /\ \E v \in vroot :
                      IF v \notin marked
                         THEN /\ marked' = marked \cup {v}
                              /\ vroot' = vroot \cup Succ[v]
                         ELSE /\ marked' = marked
                              /\ vroot' = vroot \ {v}
               /\ pc' = "a"

(* Allow stuttering after termination to avoid deadlock *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    a \/ Terminating

(* Full specification, with weak fairness on the algorithmic step *)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(a)

Termination ==
    <> (pc = "Done")

(* Type correctness invariant *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* Reachability invariant: all successors of a marked node are either already marked
   or present in vroot *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* Invariant relating marked and vroot to the ReachableFrom operator *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(* Convenience invariant stating that the algorithm computes Reachable *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* Partial correctness theorem: when the algorithm terminates, marked equals Reachable *)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

=============================================================================