---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.        *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

\* ----------------------------------------------------------------------
\* Action a  (the main loop)
\* ----------------------------------------------------------------------
a ==
    \/ /\ pc = "a"
          /\ vroot = {}
          /\ pc' = "Done"
          /\ UNCHANGED << marked, vroot >>
    \/ /\ pc = "a"
          /\ vroot # {}
          /\ \E v \in vroot :
                IF v \notin marked
                   THEN /\ marked' = marked \cup {v}
                        /\ vroot' = vroot \cup Succ[v]
                        /\ pc' = "a"
                ELSE /\ marked' = marked
                     /\ vroot' = vroot \ {v}
                     /\ pc' = "a"

\* ----------------------------------------------------------------------
\* Termination stuttering step (optional, allows infinite stuttering)
\* ----------------------------------------------------------------------
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety invariant (used for TLC)
\* ----------------------------------------------------------------------
SafetyInv == (marked = Reachable)

=============================================================================