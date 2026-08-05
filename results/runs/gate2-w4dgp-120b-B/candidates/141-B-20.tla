---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME Root \in Nodes

Reachable == ReachableFrom({Root})
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

\* Misra's variant adds every node in Succ[v] to vroot, not just those
\* not already marked; as a consequence `marked' and `vroot' can overlap,
\* so this action never removes the node it just marked.
a == /\ pc = "a"
     /\ IF vroot /= {}
          THEN /\ \E v \in vroot :
                    /\ pc' = "a"
                    /\ IF v \notin marked
                         THEN /\ marked' = marked \cup {v}
                              /\ vroot' = vroot \cup Succ[v]
                         ELSE /\ marked' = marked
                              /\ vroot' = vroot \ {v}
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>

\* Once pc = "Done" the system must not deadlock, so it is allowed to
\* stutter forever.
Terminating == /\ pc = "Done"
                /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(a)

TypeOK == /\ marked \subseteq Nodes
          /\ vroot \subseteq Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

\* Every node reachable from a node in `marked' is either marked already
\* or is reachable from some node in vroot.
Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

\* Convenience: this is the algorithm's answer.
Inv3 == Reachable = (marked \cup ReachableFrom(vroot))

Termination == <>(pc = "Done")
====