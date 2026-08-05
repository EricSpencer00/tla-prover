---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssume == Root \in Nodes

Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

a ==
    /\ pc = "a"
    /\ (IF vroot = {}
           THEN /\ pc' = "Done"
                /\ UNCHANGED << marked, vroot >>
           ELSE /\ \E v \in vroot :
                     /\ marked' = IF v \in marked THEN marked ELSE marked \cup {v}
                     /\ vroot' = IF v \in marked THEN vroot \ {v} ELSE vroot \cup Succ[v]
                /\ pc' = "a")
    /\ UNCHANGED {}

Spec == Init /\ [][a]_vars

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

PartialCorrectness == (pc = "Done") => (marked = Reachable)

====