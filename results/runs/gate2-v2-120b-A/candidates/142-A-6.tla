---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root

(***************************************************************************)
(*  Definitions from the sequential reachability algorithm module           *)
(***************************************************************************)

VARIABLES marked, frontier, pc

(* Type correctness *)
TypeCorrect ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"Done", "Running"}

(* Initial state (mirrors the algorithm's Init) *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

(***************************************************************************)
(*  Reachability helper functions                                        *)
(***************************************************************************)

(* Direct successors of a node *)
Succ == [n \in Nodes |-> {}] \* Placeholder; concrete definition must be supplied in the extending module.

(* The set of nodes reachable from a set s in zero or more steps *)
ReachableFrom(s) ==
    LET Reach(s) ==
        UNION { {n} \cup (Succ[n]) : n \in s }
    IN
        s \cup (ReachableFrom( Reach(s) ))

(* For the purpose of this module we define ReachableFrom as the reflexive
   transitive closure of Succ.  The operator is used only inside invariant
   formulas, so its concrete definition can be provided by the module that
   extends this one. *)
ReachableFrom(s) == 
    (* Reflexive transitive closure of Succ *)
    { n \in Nodes : 
        \E p \in Seq(Nodes) :
            /\ Len(p) > 0
            /\ p[1] \in s
            /\ p[Len(p)] = n
            /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]] }

(***************************************************************************)
(*  Actions                                                              *)
(***************************************************************************)

(* Add a successor of a marked node that is not yet marked *)
AddSuccessor ==
    \E n \in marked :
        \E s \in Succ[n] :
            /\ s \notin marked
            /\ s \notin frontier
            /\ frontier' = frontier \cup {s}
            /\ UNCHANGED <<marked, pc>>

(* Process the frontier: move all frontier nodes to marked *)
ProcessFrontier ==
    /\ frontier # {}
    /\ marked'   = marked \cup frontier
    /\ frontier' = {}
    /\ pc'       = IF frontier' = {} THEN "Done" ELSE "Running"
    /\ UNCHANGED pc

(* Stutter step when algorithm is done *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next ==
    \/ AddSuccessor
    \/ ProcessFrontier
    \/ Done

(***************************************************************************)
(*  Specification                                                        *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(***************************************************************************)
(*  Invariants                                                            *)
(***************************************************************************)

(* Invariant 1: type correctness + every successor of a marked node is
   either already marked or in the frontier. *)
Inv1 ==
    /\ TypeCorrect
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Invariant 2: marked ∪ ReachableFrom(frontier) = ReachableFrom(marked ∪ frontier) *)
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

(* Invariant 3: ReachableFrom({Root}) = marked \cup ReachableFrom(frontier) *)
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(***************************************************************************)
(*  Safety theorem (partial correctness)                                 *)
(***************************************************************************)

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = ReachableFrom({Root})

=============================================================================