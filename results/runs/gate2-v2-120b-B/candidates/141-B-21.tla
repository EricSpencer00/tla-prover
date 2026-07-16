---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* ------------------------------------------------------------------------- *)
(* Reachable is defined to be the set of nodes reachable from Root.          *)
(* ------------------------------------------------------------------------- *)
Reachable == ReachableFrom({Root})

(* ------------------------------------------------------------------------- *)
(* Variables:                                                              *)
(*   marked – set of nodes already confirmed reachable                     *)
(*   vroot  – frontier set of candidate nodes                              *)
(*   pc     – control variable for the algorithm (phase identifier)       *)
(* ------------------------------------------------------------------------- *)
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(* ------------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* ------------------------------------------------------------------------- *)
(* Action a: Misra's variant of BFS                                        *)
(*   - Choose an arbitrary node v from vroot.                              *)
(*   - If v is not yet marked, add it to marked and union its successors   *)
(*     into vroot (keeping v in vroot).                                    *)
(*   - If v is already marked, simply remove it from vroot.                *)
(*   - pc stays "a".                                                        *)
(* ------------------------------------------------------------------------- *)
A ==
    /\ pc = "a"
    /\ vroot # {}
    /\ \E v \in vroot :
         IF v \notin marked
            THEN /\ marked' = marked \cup {v}
                 /\ vroot' = vroot \cup Succ[v]
            ELSE /\ marked' = marked
                 /\ vroot' = vroot \ {v}
    /\ pc' = "a"
    /\ UNCHANGED << >>

(* ------------------------------------------------------------------------- *)
(* Termination action: set pc to "Done" when vroot is empty.                *)
(* ------------------------------------------------------------------------- *)
Done ==
    /\ pc = "a"
    /\ vroot = {}
    /\ pc' = "Done"
    /\ UNCHANGED << marked, vroot >>

Terminating ==
    pc = "Done" /\ UNCHANGED vars

Next ==
    A
    \/ Done
    \/ Terminating

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

(* ------------------------------------------------------------------------- *)
(* Type correctness invariant                                               *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* ------------------------------------------------------------------------- *)
(* Invariant 1: Successors of marked nodes stay within marked ∪ vroot      *)
(* ------------------------------------------------------------------------- *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* ------------------------------------------------------------------------- *)
(* Invariant 2: Reachability relationship between marked and vroot         *)
(* ------------------------------------------------------------------------- *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(* ------------------------------------------------------------------------- *)
(* Invariant 3: Relationship between marked, vroot, and Reachable          *)
(* ------------------------------------------------------------------------- *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

PartialCorrectness == (pc = "Done") => (marked = Reachable)

(* ------------------------------------------------------------------------- *)
(* Theorem statements (kept for documentation)                             *)
(* ------------------------------------------------------------------------- *)
THEOREM Spec => []PartialCorrectness

=============================================================================