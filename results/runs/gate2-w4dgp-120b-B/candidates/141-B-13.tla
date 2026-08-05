---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssume == Root \in Nodes

Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot /= {}
           THEN /\ \E v \in vroot :
                   IF v \notin marked
                      THEN /\ marked' = marked \cup {v}
                           /\ vroot' = vroot \cup Succ[v]
                           /\ pc' = pc
                      ELSE /\ marked' = marked
                           /\ vroot' = vroot \ {v}
                           /\ pc' = pc
                /\ UNCHANGED pc
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << marked, vroot >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)

Termination == <>(pc = "Done")

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

TypeOKInv == TypeOK

SpecTypeOKInv == Spec /\ []Inv1 /\ []Inv2 /\ []Inv3

PartialCorrectness ==
    SpecTypeOKInv => (pc = "Done" => marked = Reachable)

THEOREM SpecTypeOKInv => []PartialCorrectness

THEOREM ASSUME IsFiniteSet(Reachable)
         PROVE Spec => <>(pc = "Done")

====