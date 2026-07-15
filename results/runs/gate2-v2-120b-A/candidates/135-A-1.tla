---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Constants assumptions (to be overridden in the .cfg file)
--------------------------------------------------------------------*)
NodeSet == Nodes
RootNode == Root

(*--------------------------------------------------------------------
  Definitions of the graph (Succ) and the bounded sequence domain (Seq)
--------------------------------------------------------------------*)
(* Succ maps every node to exactly two distinct successors *)
SuccAssumption == 
    \A n \in NodeSet : 
        /\ Succ[n] \in SUBSET NodeSet
        /\ Cardinality(Succ[n]) = 2

(* Seq is the set of all sequences over NodeSet whose length is at most 
   the number of nodes.  This provides a finite bound for path quantification. *)
SeqSet == { s \in Seq(NodeSet) : Len(s) <= Cardinality(NodeSet) }

(*--------------------------------------------------------------------
  Initial state (inherited from the sequential reachability algorithm)
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {RootNode}
    /\ pc = "Init"

(*--------------------------------------------------------------------
  Transition relation (inherited from the sequential reachability algorithm)
--------------------------------------------------------------------*)
Next ==
    \/ /\ pc = "Init"
       /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
            /\ pc' = "Iter"
    \/ /\ pc = "Iter"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED << marked, frontier >>
    \/ /\ pc = "Done"
       /\ UNCHANGED << marked, frontier, pc >>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Helper definitions for the safety invariants
--------------------------------------------------------------------*)
(* All marked nodes are reachable via some bounded sequence from Root *)
ReachableFromRoot ==
    \A n \in marked :
        \E s \in SeqSet :
            /\ Len(s) >= 1
            /\ s[1] = RootNode
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]

(* Successor closure: every successor of a marked node is either marked or in frontier *)
SuccessorClosure ==
    \A n \in marked :
        \A s \in Succ[n] :
            s \in marked \/ s \in frontier

(* Reachable set equality: the set of nodes reachable via bounded sequences 
   equals the union of marked and frontier *)
ReachableSetEquality ==
    { n \in NodeSet :
        \E s \in SeqSet :
            /\ Len(s) >= 1
            /\ s[1] = RootNode
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
    } = marked \cup frontier

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ pc \in {"Init", "Iter", "Done"}

Inv1 == ReachableFromRoot
Inv2 == SuccessorClosure
Inv3 == ReachableSetEquality

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = { n \in NodeSet : 
                    \E s \in SeqSet :
                        /\ Len(s) >= 1
                        /\ s[1] = RootNode
                        /\ s[Len(s)] = n
                        /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
                }

(*--------------------------------------------------------------------
  Liveness property: termination
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

====