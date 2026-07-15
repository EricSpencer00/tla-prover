---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (must be supplied in the .cfg)
-----------------------------------------------------------------*)
CONSTANT Nodes
CONSTANT Root

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Succ == [n \in Nodes |-> {}] \* concrete graph should be supplied in cfg
Reachable(s) == RECURSIVE Reachable(_)
  Reachable(s) == 
    IF s = {} THEN {} 
    ELSE s \cup Reachable({ n \in Nodes : \E m \in s : n \in Succ[m] })
\* For the purpose of this proof module we only need its specification
\* not its concrete computation.

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Explore"

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
Explore ==
  /\ pc = "Explore"
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup Succ[n]
        /\ pc' = "Explore"
  /\ UNCHANGED << >>

Terminate ==
  /\ pc = "Explore"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED << marked, frontier >>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED << marked, frontier, pc >>

Next ==
  \/ Explore
  \/ Terminate
  \/ Done

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants (as required by the description)
-----------------------------------------------------------------*)
(* Invariant 1: type correctness plus each successor of a marked node
   is either already marked or in the frontier. *)
Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Explore", "Done"}
  /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Invariant 2: marked U Reachable(frontier) = Reachable(marked U frontier) *)
Inv2 ==
  marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

(* Invariant 3: Reachable({Root}) = marked \cup Reachable(frontier) *)
Inv3 ==
  Reachable({Root}) = marked \cup Reachable(frontier)

THEOREM PartialCorrectness ==
  Spec => [](pc = "Done" => marked = Reachable({Root}))

====