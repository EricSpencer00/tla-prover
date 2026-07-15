---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

(* ---------------------------------------------------------------------- *)
(* State variables inherited from the sequential reachability algorithm   *)
(* ---------------------------------------------------------------------- *)

VARIABLES marked, frontier, pc

(* ---------------------------------------------------------------------- *)
(* Type definitions                                                       *)
(* ---------------------------------------------------------------------- *)

NodeSet == Nodes
SeqSet  == Seq

(* ---------------------------------------------------------------------- *)
(* Initial state (could be overridden in a .cfg)                          *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Init"

(* ---------------------------------------------------------------------- *)
(* Actions (mirroring the sequential algorithm)                           *)
(* ---------------------------------------------------------------------- *)

AddFrontier ==
    /\ pc = "Init"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
    /\ pc' = "Running"

Done ==
    /\ pc = "Running"
    /\ frontier = {}
    /\ marked' = marked
    /\ frontier' = frontier
    /\ pc' = "Done"

Next == AddFrontier \/ Done

(* ---------------------------------------------------------------------- *)
(* Specification                                                          *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ---------------------------------------------------------------------- *)
(* Safety invariants (as per the description)                             *)
(* ---------------------------------------------------------------------- *)

(* Type correctness *)
TypeOK ==
    /\ marked   \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ pc \in {"Init", "Running", "Done"}

(* Inv1: Successor closure (all successors of marked nodes are either marked or in frontier) *)
Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

(* Inv2: Reachability decomposition (every node is either marked, in frontier, or unreachable) *)
Inv2 ==
    \A n \in NodeSet :
        n \in marked \/ n \in frontier \/ 
        \A p \in SeqSet : ~ /\ Len(p) > 0
                           /\ p[1] = Root
                           /\ p[Len(p)] = n
                           /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]]

(* Inv3: Reachable set equality (marked equals the set of nodes reachable from Root) *)
Inv3 ==
    marked = { n \in NodeSet :
                \E p \in SeqSet :
                    /\ Len(p) > 0
                    /\ p[1] = Root
                    /\ p[Len(p)] = n
                    /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]] }

(* Partial correctness: if the algorithm terminates, all nodes reachable from Root are marked *)
PartialCorrectness ==
    pc = "Done" => marked = { n \in NodeSet :
                               \E p \in SeqSet :
                                   /\ Len(p) > 0
                                   /\ p[1] = Root
                                   /\ p[Len(p)] = n
                                   /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]] }

(* ---------------------------------------------------------------------- *)
(* Liveness property (termination)                                        *)
(* ---------------------------------------------------------------------- *)

Termination == <> (pc = "Done")

====