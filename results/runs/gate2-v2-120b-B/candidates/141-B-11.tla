---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* ---------------------------------------------------------------------- *)
(* Reachable is the set of nodes reachable from Root.                      *)
(* ---------------------------------------------------------------------- *)
Reachable == ReachableFrom({Root})

(* ---------------------------------------------------------------------- *)
(* Variables of the algorithm.                                            *)
(* ---------------------------------------------------------------------- *)
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(* ---------------------------------------------------------------------- *)
(* Initial state.                                                         *)
(* ---------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* ---------------------------------------------------------------------- *)
(* Action a implements the algorithm described in the PlusCal code.      *)
(* It is split into two mutually exclusive cases, each of which fully    *)
(* specifies the values of all variables, thereby preventing the          *)
(* “variable not assigned” error reported by TLC.                         *)
(* ---------------------------------------------------------------------- *)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
                /\ UNCHANGED << marked, vroot >>
          ELSE
          /\ \E v \in vroot :
                /\ IF v \notin marked
                      THEN /\ marked' = marked \cup {v}
                           /\ vroot'  = vroot \cup Succ[v]
                           /\ pc' = "a"
                      ELSE /\ marked' = marked
                           /\ vroot'  = vroot \ {v}
                           /\ pc' = "a"

(* ---------------------------------------------------------------------- *)
(* Allow infinite stuttering after termination.                           *)
(* ---------------------------------------------------------------------- *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ a
    \/ Terminating

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(a)

Termination == <> (pc = "Done")

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant.                                            *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* ---------------------------------------------------------------------- *)
(* Invariant Inv1: each node’s successors stay within marked ∪ vroot.      *)
(* ---------------------------------------------------------------------- *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* ---------------------------------------------------------------------- *)
(* Invariant Inv2: relationship between marked, vroot, and ReachableFrom. *)
(* ---------------------------------------------------------------------- *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(* ---------------------------------------------------------------------- *)
(* Invariant Inv3: connects the algorithm’s state to the specification.  *)
(* ---------------------------------------------------------------------- *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* ---------------------------------------------------------------------- *)
(* Partial correctness theorem (already present in original spec).       *)
(* ---------------------------------------------------------------------- *)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

====