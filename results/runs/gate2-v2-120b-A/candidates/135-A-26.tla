---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

(* --algorithmic overview of the sequential Misra reachability algorithm --
   Variables:
     marked   : set of Nodes that have been discovered
     frontier : set of Nodes that are discovered but whose successors
                have not yet been processed
     pc       : program counter indicating which step of the algorithm
                we are in ("Init", "Loop", or "Done").
*)

(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(* The main loop body *)
Process ==
    /\ pc = "Loop"
    /\ frontier # {}
    /\ LET n == CHOOSE x \in frontier : TRUE IN
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
       /\ pc' = "Loop"
    /\ UNCHANGED << >>

(* Transition to done when frontier empty *)
Done ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

(* Stuttering step to keep model finite after termination *)
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

NEXT ==
    \/ Process
    \/ Done
    \/ Stutter

(* Specification *)
Spec == Init /\ [][NEXT]_<<marked, frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Loop", "Done"}

(* Successor closure invariant: every marked node's successors are either
   already marked or currently in the frontier. *)
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Reachability decomposition invariant: the union of marked and frontier
   equals the set of nodes that are reachable from Root via some sequence
   (path) of length at most Seq. *)
Inv2 ==
    marked \cup frontier =
        { n \in Nodes : \E s \in Seq :
            /\ Len(s) <= Len(Seq)
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

(* Reachable set equality invariant: the set of nodes reachable from the
   root in the underlying graph equals the set of marked nodes when the
   algorithm has terminated. *)
Inv3 ==
    (pc = "Done") => (marked = { n \in Nodes : \E s \in Seq :
                                 /\ Len(s) <= Len(Seq)
                                 /\ s[1] = Root
                                 /\ s[Len(s)] = n
                                 /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] })

(* Partial correctness: when the algorithm finishes, every node that is
   reachable from the root (by a path of length at most Seq) is in the
   marked set, and no unreachable node is marked. *)
PartialCorrectness ==
    (pc = "Done") => (marked = { n \in Nodes : \E s \in Seq :
                                 /\ Len(s) <= Len(Seq)
                                 /\ s[1] = Root
                                 /\ s[Len(s)] = n
                                 /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] })

(* Termination: eventually the algorithm reaches the Done state. *)
Termination == <> (pc = "Done")

====