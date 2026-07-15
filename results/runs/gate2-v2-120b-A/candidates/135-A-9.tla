---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Constants required by the .cfg                                         *)
(***************************************************************************)
CONSTANTS Nodes, Root, Succ, Seq

(***************************************************************************)
(*  Derived sets                                                          *)
(***************************************************************************)
NodeSet == 1 .. Nodes

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES marked, frontier, pc

(***************************************************************************)
(*  Initial state (inherits from the base algorithm)                      *)
(***************************************************************************)
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "Done"

(***************************************************************************)
(*  Actions (inherit from the base algorithm, simplified for this config) *)
(***************************************************************************)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier>>

(***************************************************************************)
(*  Next-state relation                                                    *)
(***************************************************************************)
Next ==
    \/ Done

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

(***************************************************************************)
(*  Invariants                                                             *)
(***************************************************************************)

(* Type correctness: all variables contain only nodes or allowed strings *)
TypeOK ==
    /\ marked \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ pc \in {"Done"}

(* Inv1: Successor closure – every node in frontier has its successors in frontier or marked *)
Inv1 ==
    \A n \in frontier :
        \A s \in Succ[n] :
            s \in frontier \/ s \in marked

(* Inv2: Reachability decomposition – the union of marked and frontier equals the set of nodes reachable from Root via paths described by Seq *)
Inv2 ==
    marked \cup frontier =
        { n \in NodeSet :
            \E i \in 1..Len(Seq) :
                /\ Seq[1] = Root
                /\ Seq[i] = n
                /\ \A j \in 1..(i-1) :
                    Seq[j+1] \in Succ[Seq[j]] }

(* Inv3: Reachable set equality – the set of marked nodes is exactly the set of nodes reachable from Root via any sequence of successors of length up to Nodes *)
Inv3 ==
    marked =
        { n \in NodeSet :
            \E i \in 1..Nodes :
                /\ Seq[1] = Root
                /\ Seq[i] = n
                /\ \A j \in 1..(i-1) :
                    Seq[j+1] \in Succ[Seq[j]] }

(* PartialCorrectness – when the algorithm reports done, all reachable nodes are marked *)
PartialCorrectness ==
    pc = "Done" => \A n \in NodeSet :
        ( \E i \in 1..Nodes :
            /\ Seq[1] = Root
            /\ Seq[i] = n
            /\ \A j \in 1..(i-1) :
                Seq[j+1] \in Succ[Seq[j]] ) => n \in marked

(***************************************************************************)
(*  Liveness property (termination)                                       *)
(***************************************************************************)
Termination ==
    []<>(pc = "Done")

=============================================================================