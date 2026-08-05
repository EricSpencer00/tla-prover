---- MODULE Reachable ----
(*  Breadth-first search for reachable nodes in a directed graph.  This
    version implements a variant due to Jayadev Misra that keeps the set
    of reached nodes disjoint from the set of frontier nodes only in the
    sense that nodes marked as reached are never also removed from the
    frontier; frontier nodes are added without regard to whether they are
    already known.  The add-to-reached step adds the node while still
    keeping it in the frontier, and the frontier is drained only of nodes
    that are already reached.  This choice matters for a parallel
    implementation.  The full safety proof is in module ReachableProofs. *)
EXTENDS Reachability, Integers, FiniteSets
CONSTANTS Root
ASSUME RootAssump == Root \in Nodes

(* Reachable is the set of nodes reachable from Root.  The algorithm is *)
(* meant to compute Reachable.                                           *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc
vars == <<marked, vroot, pc>>

Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

a ==
    /\ pc = "a"
    /\ IF vroot = {}
         THEN /\ pc' = "Done"
              /\ UNCHANGED <<marked, vroot>>
         ELSE \/ \E v \in vroot :
                    /\ marked' = IF v \in marked THEN marked
                                 ELSE marked \cup {v}
                    /\ vroot' = IF v \in marked
                                 THEN vroot \ {v}
                                 ELSE vroot \cup Succ[v]
               /\ pc' = "a"
    /\ UNCHANGED pc

(* Allow infinite stuttering once the algorithm has finished. *)
Terminating == pc = "Done" /\ UNCHANGED vars
Next == a \/ Terminating

Spec == Init /\ [][Next]_vars
        /\ WF_vars(a)
Termination == <>(pc = "Done")

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot))
          = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = (marked \cup ReachableFrom(vroot))

PartialCorrectness == (pc = "Done") => (marked = Reachable)
THEOREM Spec => []PartialCorrectness

THEOREM ASSUME IsFiniteSet(Reachable)
         PROVE Spec => <>(pc = "Done")
====