---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* concrete definitions for the constants *)
ASSUME Nodes = {"a","b","c","d"}
ASSUME Root \in Nodes
ASSUME Succ = [n \in Nodes |-> 
          CASE n = "a" -> {"b","c"}
               [] n = "b" -> {"c","d"}
               [] n = "c" -> {"a","d"}
               [] n = "d" -> {"a","b"}
               [] OTHER   -> {}]

(* operator that the .cfg substitutes for Succ.
   It must be a constant (function) of the same arity as Succ. *)
ConnectedToSomeButNotAll == 
    [n \in Nodes |-> 
          CASE n = "a" -> {"b","c"}
               [] n = "b" -> {"c","d"}
               [] n = "c" -> {"a","d"}
               [] n = "d" -> {"a","b"}
               [] OTHER   -> {}]

(* bounded sequence operator, replaces Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

Next ==
    \/ /\ pc = "start"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
            /\ pc'       = "start"
    \/ /\ pc = "start"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* invariants *)
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc       \in {"start","done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup frontier \subseteq Nodes

Reachable ==
    { n \in Nodes :
        \E seq \in LimitedSeq(Nodes) :
            /\ Len(seq) >= 1
            /\ seq[1] = Root
            /\ seq[Len(seq)] = n
            /\ \A i \in 1 .. (Len(seq)-1) :
                 seq[i+1] \in Succ[seq[i]] }

Inv3 == marked \cup frontier = Reachable

PartialCorrectness ==
    (pc = "done") => (marked = Reachable)

Termination == <> (pc = "done")
====