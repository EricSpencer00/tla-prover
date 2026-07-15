---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*----------------------------------------------------------------------
  Constants (provided by the .cfg file)
  ----------------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* The finite set of graph nodes
    Root,    \* The distinguished start node
    Succ,    \* Function mapping each node to its two successors
    Seq      \* Set of finite sequences over Nodes, bounded length

(*----------------------------------------------------------------------
  Derived sets
  ----------------------------------------------------------------------*)
Node == Nodes

(*----------------------------------------------------------------------
  State variables (inherited from the sequential algorithm)
  ----------------------------------------------------------------------*)
VARIABLES
    marked,   \* Set of nodes known to be reachable
    frontier, \* Set of nodes whose successors are to be explored
    pc        \* Program counter (identifies the current step of the algorithm)

(*----------------------------------------------------------------------
  Initialization (inherited)
  ----------------------------------------------------------------------*)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Explore"

(*----------------------------------------------------------------------
  Actions (inherited)
  ----------------------------------------------------------------------*)
Explore ==
    /\ pc = "Explore"
    /\ \E n \in frontier :
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup Succ[n]
          /\ pc'       = "Explore"
    /\ UNCHANGED << >>

Done ==
    /\ pc = "Explore"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED << marked, frontier >>

Next ==
    \/ Explore
    \/ Done
    \/ (pc = "Done" /\ UNCHANGED << marked, frontier, pc >>)

(*----------------------------------------------------------------------
  Specification
  ----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*----------------------------------------------------------------------
  Safety invariants
  ----------------------------------------------------------------------*)
(* Type correctness: all variables have the expected types *)
TypeOK ==
    /\ marked   \in SUBSET Node
    /\ frontier \in SUBSET Node
    /\ pc       \in {"Explore", "Done"}

(* Inv1: Successor closure – every node in the frontier has all its
   successors within the allowed node set. *)
Inv1 ==
    /\ frontier \subseteq Node
    /\ \A n \in frontier : Succ[n] \subseteq Node

(* Inv2: Reachability decomposition – the union of marked and frontier
   is always a subset of the nodes that are reachable from Root via a
   sequence in Seq. *)
Inv2 ==
    \A n \in marked \cup frontier :
        \E s \in Seq :
            Len(s) > 0 /\ s[1] = Root /\ s[Len(s)] = n /\
            \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]

(* Inv3: Reachable set equality – every node reachable from Root by a
   bounded sequence is eventually either marked or waiting in the
   frontier. *)
Inv3 ==
    \A n \in Node :
        (\E s \in Seq :
            Len(s) > 0 /\ s[1] = Root /\ s[Len(s)] = n /\
            \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]])
        => n \in marked \cup frontier

(* Partial correctness – when the algorithm terminates, the marked set
   exactly equals the set of nodes reachable from Root via a bounded
   sequence. *)
PartialCorrectness ==
    pc = "Done" => marked = { n \in Node :
        \E s \in Seq :
            Len(s) > 0 /\ s[1] = Root /\ s[Len(s)] = n /\
            \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

(*----------------------------------------------------------------------
  Liveness property (termination)
  ----------------------------------------------------------------------*)
Termination ==
    <> (pc = "Done")

=============================================================================