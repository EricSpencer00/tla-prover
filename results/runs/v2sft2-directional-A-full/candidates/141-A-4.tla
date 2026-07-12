---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

(* --------------------------------------------------------------------- *)
(* Type correctness invariant                                            *)
(* --------------------------------------------------------------------- *)
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "terminated"}

(* --------------------------------------------------------------------- *)
(* Initial state                                                         *)
(* --------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(* --------------------------------------------------------------------- *)
(* Main loop action                                                      *)
(* --------------------------------------------------------------------- *)
Main ==
    /\ pc = "run"
    /\ frontier # {}
    /\ \E v \in frontier :
           IF v \notin marked THEN
              /\ marked' = marked \cup {v}
              /\ frontier' = frontier \cup (Succ[v])
              /\ pc' = pc
           ELSE
              /\ frontier' = frontier \ {v}
              /\ marked' = marked
              /\ pc' = pc

(* --------------------------------------------------------------------- *)
(* Termination action                                                    *)
(* --------------------------------------------------------------------- *)
Terminate ==
    /\ pc = "run"
    /\ frontier = {}
    /\ pc' = "terminated"
    /\ UNCHANGED <<marked, frontier>>

(* --------------------------------------------------------------------- *)
(* Next-state relation                                                   *)
(* --------------------------------------------------------------------- *)
Next == 
    \/ Main
    \/ Terminate

(* --------------------------------------------------------------------- *)
(* Specification                                                         *)
(* --------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* --------------------------------------------------------------------- *)
(* Invariants (partial correctness and auxiliary properties)             *)
(* --------------------------------------------------------------------- *)
(* 1. Every successor of a marked node is either marked or in the frontier *)
Inv1 ==
    \A v \in marked :
        (\A w \in Succ[v] : w \in marked \/ w \in frontier)

(* 2. The union of marked and frontier equals the set of nodes reachable
    from the union of marked and frontier *)
Inv2 ==
    reachable[Nodes, Succ, marked \cup frontier] = marked \cup frontier

(* 3. The nodes reachable from the root equal the marked set plus
    nodes reachable from the frontier *)
Inv3 ==
    reachable[Nodes, Succ, {Root}] = marked \cup reachable[Nodes, Succ, frontier]

(* 4. Auxiliary: the marked set is a subset of reachable nodes from the root *)
Inv4 == marked \subseteq reachable[Nodes, Succ, {Root}]

(* 5. Partial correctness (combination of Inv1, Inv3, and Termination) *)
PartialCorrectness ==
    /\ pc = "terminated"
    /\ marked = reachable[Nodes, Succ, {Root}]

(* --------------------------------------------------------------------- *)
(* Properties                                                            *)
(* --------------------------------------------------------------------- *)
Termination ==
    WF_INIT WF_NEXT

(* --------------------------------------------------------------------- *)
(* Helper definition of transitive closure of Succ over a set S *)
(* --------------------------------------------------------------------- *)
REACH(S) == 
    REACH_F(S, {})

REACH_F(S, Visited) ==
    IF S = {} THEN Visited
    ELSE
        REACH_F(S \ Visited, Visited \cup {S} \cup (Succ[Visited]))

(* --------------------------------------------------------------------- *)
(* The reachable function used in the invariants                         *)
(* --------------------------------------------------------------------- *)
reachable[Nodes, Succ, S] == REACH_F(S, {})

(* --------------------------------------------------------------------- *)
(* The module ends here                                                   *)
(* --------------------------------------------------------------------- *)

====