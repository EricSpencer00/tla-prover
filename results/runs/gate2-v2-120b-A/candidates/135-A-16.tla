---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants required by the .cfg file
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*-----------------------------------------------------------------
  State variables (inherited from the sequential reachability algorithm)
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Derived definitions
-----------------------------------------------------------------*)
NodeSet == Nodes
SeqSet  == Seq

(*-----------------------------------------------------------------
  Initial state (inherited, instantiated with concrete graph)
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(*-----------------------------------------------------------------
  Actions (inherited, unchanged)
-----------------------------------------------------------------*)
Step ==
    /\ pc = "Init"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup { m \in Succ[n] : m \notin marked }
    /\ pc' = "Step"

Done ==
    /\ pc = "Step"
    /\ frontier = {}
    /\ UNCHANGED <<marked, frontier>>
    /\ pc' = "Done"

Next == Step \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
(* Type correctness *)
TypeOK ==
    /\ marked \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ pc \in {"Init", "Step", "Done"}

(* Successor closure: every node in frontier has a predecessor in marked *)
Inv1 ==
    \A n \in frontier :
        \E p \in marked : n \in Succ[p]

(* Reachability decomposition: marked is exactly the set of nodes reachable from Root via a bounded sequence *)
ReachableFromRoot ==
    \E s \in SeqSet :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
        /\ s[Len(s)] = n

Inv2 ==
    marked = { n \in NodeSet : ReachableFromRoot }

(* Reachable set equality: frontier is the set of nodes reachable from marked but not yet marked *)
Inv3 ==
    frontier = { n \in NodeSet :
                    \E p \in marked : n \in Succ[p] /\ n \notin marked }

(* Partial correctness: when the algorithm terminates, every node reachable from Root is in marked *)
PartialCorrectness ==
    pc = "Done" => marked = { n \in NodeSet : ReachableFromRoot }

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================