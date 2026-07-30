---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

\* Configuration module: concrete graph and a bounded sequence override for
\* model checking the standard reachability algorithm.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "searching", "completed"}

\* The reachability invariant the original algorithm proved under an
\* unrestricted (infinite) definition of Seq.
\* Here Succ is concretized and Seq is bounded (FiniteSeq) so TLC can explore
\* the entire reachable state space.

FiniteSeq(S) == UNION { Seq(S) : k \in 1..Cardinality(S) }
Inv1 == \A n \in Nodes : n \in marked => \E s \in FiniteSeq(Nodes) :
    /\ Len(s) > 0
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in Succ[s[i]]

Inv2 == \A x \in Nodes : x \in marked => frontier \subseteq Succ[x]
Inv3 == \A x \in frontier : marked \cup (Succ[x] \cup {x}) \subseteq marked
PartialCorrectness == marked = Nodes

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore ==
    /\ pc = "searching"
    /\ \E x \in frontier :
        /\ marked' = marked \cup Succ[x]
        /\ frontier' = Succ[x] \cup {x}
    /\ pc' = "searching"

Start == /\ pc = "idle" /\ pc' = "searching" /\ UNCHANGED <<marked, frontier>>
Done == /\ pc = "searching" /\ frontier = {} /\ pc' = "completed" /\ UNCHANGED <<marked, frontier>>
Idle == pc = "completed" /\ UNCHANGED vars

Next == Start \/ Explore \/ Done \/ Idle

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "completed")

End == (marked = Nodes) /\ (pc = "completed")
Also == End

ConnectedToSomeButNotAll == \E y \in Nodes : y \in Succ[Root]

\* The .cfg file replaces the default infinite Seq with this bounded finite
\* version; the override is only useful if the model explicitly keeps the
\* original definition around (as FiniteSeq above).
\* No DECLARE for "Seq" -- just ensure the override is in the spec.
\* The overridden definition is not itself part of the model.
====