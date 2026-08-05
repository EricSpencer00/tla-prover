---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc
vars == << marked, vroot, pc >>

Next == \/ /\ pc = "a"
             /\ IF vroot /= {}
                  THEN \/ \E v \in vroot :
                            IF v \notin marked
                               THEN /\ marked' = marked \cup {v}
                                    /\ vroot' = vroot \cup Succ[v]
                                    /\ pc' = "a"
                               ELSE /\ vroot' = vroot \ {v}
                                    /\ marked' = marked
                                    /\ pc' = "a"
                       \/ /\ vroot = {}
                          /\ pc' = "Done"
                          /\ UNCHANGED << marked, vroot >>
             /\ UNCHANGED pc
       \/ /\ pc = "Done" /\ UNCHANGED vars

Spec == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"
        /\ [][Next]_vars
        /\ WF_vars(Next)

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

PartialCorrectness == (pc = "Done") => (marked = Reachable)

Termination == <>(pc = "Done")

====