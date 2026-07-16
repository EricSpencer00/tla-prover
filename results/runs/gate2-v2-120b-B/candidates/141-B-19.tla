---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.       *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

\* ----------------------------------------------------------------------
\* Helper definition for the tuple of state variables
\* ----------------------------------------------------------------------
vars == << marked, vroot, pc >>

(***************************************************************************)
(* Initial state: no nodes are marked, vroot contains only the Root, and   *)
(* control variable pc is set to "a".                                      *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(***************************************************************************)
(* The main step of the algorithm, labelled "a".  It corresponds to the   *)
(* PlusCal action described in the comments of the original spec.  The   *)
(* step may either add a node v from vroot to marked (and expand vroot   *)
(* with Succ[v]), or remove a node v that is already marked from vroot.  *)
(* In both cases the control variable pc remains "a".                     *)
(***************************************************************************)
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
                    ELSE /\ vroot' = vroot \ {v}
                         /\ marked' = marked
                         /\ pc' = "a"
               /\ UNCHANGED <<>>

(***************************************************************************)
(* Allow infinite stuttering after termination to avoid deadlock.         *)
(***************************************************************************)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(a)

\* ----------------------------------------------------------------------
\* Type correctness invariant (kept from the original spec)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

\* ----------------------------------------------------------------------
\* Partial correctness invariant (Inv3 from the original spec)
\* ----------------------------------------------------------------------
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

\* ----------------------------------------------------------------------
\* Theorems (kept unchanged)
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "Done") => (marked = Reachable)
THEOREM Spec => []PartialCorrectness

(***************************************************************************)
(* Liveness theorem (unchanged)                                            *)
(***************************************************************************)
THEOREM ASSUME IsFiniteSet(Reachable) PROVE Spec => <>(pc = "Done")

====