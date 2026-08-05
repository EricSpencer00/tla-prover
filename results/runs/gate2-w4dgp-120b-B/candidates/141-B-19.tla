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
     /\ vroot # {}
     /\ \E v \in vroot :
          /\ IF v \notin marked
               THEN /\ marked' = marked \cup {v}
                    /\ vroot' = vroot \cup Succ[v]
               ELSE /\ vroot' = vroot \ {v}
                    /\ UNCHANGED marked
          /\ pc' = "a"

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

Termination == <>(pc = "Done")

TypeInv == []TypeOK

Inv1Inv == []Inv1

Inv2Inv == []Inv2

Inv3Inv == []Inv3

PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => PartialCorrectness

TerminationAssumesFinite == ASSUME IsFiniteSet(Reachable)
                            PROVE Spec => <>(pc = "Done")
====