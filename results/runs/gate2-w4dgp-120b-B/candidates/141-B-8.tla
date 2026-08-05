---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssume == Root \in Nodes

Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

TypeOK == /\ marked \subseteq Nodes
          /\ vroot \subseteq Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

Next == /\ pc = "a"
        /\ \/ (\E v \in vroot :
                /\ IF v \notin marked
                     THEN /\ marked' = marked \cup {v}
                          /\ vroot' = vroot \cup Succ[v]
                     ELSE /\ vroot' = vroot \ {v}
                          /\ UNCHANGED marked
                /\ UNCHANGED pc)
           \/ /\ vroot = {}
              /\ pc' = "Done"
              /\ UNCHANGED << marked, vroot >>
Spec == Init /\ [][Next]_vars

PartialCorrect == (pc = "Done") => (marked = Reachable)

====