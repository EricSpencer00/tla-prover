---- MODULE Reachable ----
EXTENDS FiniteSets, Sequences, TLC

(*---------------------------------------------------------------------*)
(*   CONSTANTS *)
CONSTANTS Nodes, Root, Succ

(*---------------------------------------------------------------------*)
(*   REPLACED OPERATORS *)
(*  ConnectedToSomeButNotAll replaces Succ in the configuration  *)
ConnectedToSomeButNotAll(n) == Succ[n]

(*  LimitedSeq replaces Seq from Sequences (finite version)        *)
LimitedSeq(S) == Seq(S)

(*---------------------------------------------------------------------*)
(*   STATE VARIABLES *)
VARIABLES marked, frontier, pc

(*---------------------------------------------------------------------*)
(*   RELATION AND REACHABILITY DEFINITION                         *)
R == { <<x, y>> : x \in Nodes /\ y \in ConnectedToSomeButNotAll[x] }

Reach(S) == TC(R, S)

(*---------------------------------------------------------------------*)
(*   INITIAL STATE                                                *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"
    /\ TypeOK

(*---------------------------------------------------------------------*)
(*   TYPE CORRECTNESS INVARIANT                                    *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}
    /\ Root \in Nodes

(*---------------------------------------------------------------------*)
(*   MAIN ACTION                                                   *)
Next ==
    \/ /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ frontier # {}
       /\ \E n \in frontier:
            \/ /\ n \notin marked
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
               /\ pc' = "Running"
            \/ /\ n \in marked
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
               /\ pc' = "Running"

(*---------------------------------------------------------------------*)
(*   SPECIFICATION                                                *)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Next)

(*---------------------------------------------------------------------*)
(*   INVARIANTS                                                   *)
(*  1. Every successor of a marked node is in marked or frontier   *)
Inv1 ==
    \A n \in marked :
        ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

(*  2. Union of marked and nodes reachable from frontier equals    *)
(*     nodes reachable from (marked ∪ frontier)                     *)
Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

(*  3. Nodes reachable from Root equal marked plus nodes reachable *)
(*     from frontier                                                *)
Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

(*  Partial correctness: when terminated, marked = reachable set *)
PartialCorrectness ==
    (frontier = {} ) => marked = Reach({Root})

(*---------------------------------------------------------------------*)
(*   LIVENESS PROPERTY                                            *)
Termination == <> (frontier = {})

====