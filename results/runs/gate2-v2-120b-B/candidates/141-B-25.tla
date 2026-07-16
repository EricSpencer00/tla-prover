---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.        *)
(* The purpose of the algorithm is to compute Reachable.                  *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

\* -----------------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------------
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

\* -----------------------------------------------------------------------
\* Initial predicate
\* -----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ vroot = {Root}
  /\ pc = "a"

\* -----------------------------------------------------------------------
\* The algorithm action, renamed to avoid shadowing the variable `v`
\* -----------------------------------------------------------------------
A(v) ==
  /\ pc = "a"
  /\ v \in vroot
  /\ IF v \notin marked
        THEN /\ marked' = marked \cup {v}
             /\ vroot'  = vroot \cup Succ[v]
        ELSE /\ marked' = marked
             /\ vroot'  = vroot \ {v}
  /\ pc' = "a"

a ==
  \/ \E v \in vroot: A(v)
  \/ /\ pc = "a"
     /\ vroot = {}
     /\ pc' = "Done"
     /\ UNCHANGED << marked, vroot >>

\* -----------------------------------------------------------------------
\* Allow infinite stuttering after termination
\* -----------------------------------------------------------------------
Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == a \/ Terminating

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

\* -----------------------------------------------------------------------
\* Invariants
\* -----------------------------------------------------------------------
TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ vroot \in SUBSET Nodes
  /\ pc \in {"a", "Done"}
  /\ (pc = "Done") => (vroot = {})

Inv1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
  (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 ==
  Reachable = marked \cup ReachableFrom(vroot)

PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

=============================================================================