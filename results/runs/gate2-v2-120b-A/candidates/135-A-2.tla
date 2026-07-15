---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the reference .cfg
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,    \* The set of all nodes (must be a finite set of natural numbers)
    Root,     \* The distinguished start node, an element of Nodes
    Succ,     \* A total function giving exactly two successors for each node
    Seq       \* Upper bound on the length of any path (overrides infinite sequences)

(*-----------------------------------------------------------------
  Derived constant: the set of all possible sequences (paths) of length ≤ Seq
-----------------------------------------------------------------*)
Path == { s \in Seq(Seq) : Len(s) <= Seq }

(*-----------------------------------------------------------------
  State variables (inherited from the sequential reachability algorithm)
-----------------------------------------------------------------*)
VARIABLES
    marked,   \* Set of nodes that have been discovered as reachable
    frontier, \* Set of nodes whose successors still need to be explored
    pc        \* Program counter, indicating the current phase of the algorithm

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
IsFinished(pc) == pc = "Done"

(* Initial state, matching the algorithm's specification with concrete graph *)
Init ==
    /\ marked   = {Root}
    /\ frontier = {Root}
    /\ pc       = "Explore"

(* One step of the algorithm: explore all successors of the current frontier *)
ExploreStep ==
    /\ pc = "Explore"
    /\ LET newFront == { y \in Nodes : 
                         \E x \in frontier : y \in Succ[x] } IN
       /\ marked   = marked \cup newFront
       /\ frontier = newFront \cup {y \in frontier : 
                         \E x \in frontier : y \in Succ[x]} \ {x \in frontier : x \in newFront}
       /\ pc       = IF frontier = {} THEN "Done" ELSE "Explore"

(* Stuttering step when the algorithm is finished *)
DoneStep ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

(* Next-state relation *)
Next == ExploreStep \/ DoneStep

(* Specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
(* Type correctness: all variables stay within their intended domains *)
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Explore", "Done"}

(* Inv1: Successor closure – every node in the frontier has all its
        successors either already marked or also in the frontier. *)
Inv1 ==
    \A x \in frontier :
        \A y \in Succ[x] : y \in marked \/ y \in frontier

(* Inv2: Reachability decomposition – every marked node is either the Root
        or reachable via a path of length ≤ Seq from the Root. *)
Inv2 ==
    \A n \in marked :
        n = Root \/ \E s \in Path :
            /\ Len(s) >= 1
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]

(* Inv3: Reachable set equality – the set of marked nodes equals the set
        of all nodes that have a path from Root respecting the length bound. *)
Inv3 ==
    marked = { n \in Nodes :
                n = Root \/ \E s \in Path :
                    /\ Len(s) >= 1
                    /\ s[1] = Root
                    /\ s[Len(s)] = n
                    /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

(* PartialCorrectness – when the algorithm finishes, the marked set is exactly
   the set of nodes reachable from Root (i.e., Inv3 holds in the final state). *)
PartialCorrectness ==
    (pc = "Done") => (marked = { n \in Nodes :
                                 n = Root \/ \E s \in Path :
                                     /\ Len(s) >= 1
                                     /\ s[1] = Root
                                     /\ s[Len(s)] = n
                                     /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] } )

(*-----------------------------------------------------------------
  Liveness property (termination)
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

====