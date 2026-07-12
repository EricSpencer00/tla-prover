---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Process", "Done"}

(* ----------------------------------------------------------------------
   Algorithm invariants (inherited from the sequential reachability algorithm)
   ---------------------------------------------------------------------- *)

(* Inv1: Successor closure – every node in frontier has all its successors
   already in marked or frontier. *)
Inv1 == 
    \A n \in frontier :
        Succ[n] \subseteq marked \cup frontier

(* Inv2: Reachability decomposition – marked is the set of nodes reachable
   from Root via any number of steps. *)
Inv2 == 
    marked = { n \in Nodes : \E seq \in Seq :
                 seq[1] = Root /\ 
                 \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ[seq[i]] /\ 
                 seq[Len(seq)] = n }

(* Inv3: Reachable set equality – frontier is exactly the set of nodes that
   are reachable from Root but not yet marked. *)
Inv3 == 
    frontier = { n \in Nodes : n \notin marked /\ 
                 \E seq \in Seq :
                     seq[1] = Root /\ 
                     \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ[seq[i]] /\ 
                     seq[Len(seq)] = n }

(* Partial correctness property – when the algorithm terminates, marked
   equals the set of all nodes reachable from Root. *)
PartialCorrectness == 
    (pc = "Done") => marked = { n \in Nodes : \E seq \in Seq :
                                 seq[1] = Root /\ 
                                 \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ[seq[i]] /\ 
                                 seq[Len(seq)] = n }

(* ----------------------------------------------------------------------
   Initial state (inherited from the algorithm specification)
   ---------------------------------------------------------------------- *)
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(* ----------------------------------------------------------------------
   Next-state relation (inherited from the algorithm specification)
   ---------------------------------------------------------------------- *)
Next == 
    \/ /\ pc = "Init"
       /\ pc' = "Process"
    \/ /\ pc = "Process"
       /\ marked' = marked \cup frontier
       /\ frontier' = { n \in Nodes : n \notin marked' /\ 
                        \E seq \in Seq :
                            seq[1] = Root /\ 
                            \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ[seq[i]] /\ 
                            seq[Len(seq)] = n }
       /\ pc' = "Done"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Termination property (liveness)
   ---------------------------------------------------------------------- *)
Termination == <> (pc = "Done")

====