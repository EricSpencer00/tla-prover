---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

\* Group the variables for convenience
vars == << marked, vroot, pc >>

\* Initial state
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

\* Action a, rewritten to assign pc in every branch
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE (* vroot is non‑empty *)
               /\ \E v \in vroot :
                     IF v \notin marked
                        THEN /\ marked' = marked \cup {v}
                             /\ vroot' = vroot \cup Succ[v]
                             /\ pc' = "a"
                        ELSE /\ marked' = marked
                             /\ vroot' = vroot \ {v}
                             /\ pc' = "a"
               /\ UNCHANGED pc

\* Allow stuttering after termination (pc = "Done")
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ a
    \/ Terminating

\* Full specification
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(a)

\* Type correctness invariant
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

\* Invariant Inv1
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

\* Invariant Inv2
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

\* Invariant Inv3
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

\* Partial correctness theorem
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

\* Liveness theorem (unchanged from original)
THEOREM  ASSUME IsFiniteSet(Reachable)
         PROVE  Spec => <>(pc = "Done")

====