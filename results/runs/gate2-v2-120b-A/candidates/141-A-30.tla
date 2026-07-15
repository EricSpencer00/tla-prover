---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (provided by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(* pc values *)
Running == "Running"
Done    == "Done"

(*-----------------------------------------------------------------
  Type correctness
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = Running

(*-----------------------------------------------------------------
  The main nondeterministic step
-----------------------------------------------------------------*)
Step ==
    /\ pc = Running
    /\ \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = Running
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = Running

(*-----------------------------------------------------------------
  Termination (when frontier empty)
-----------------------------------------------------------------*)
Terminate ==
    /\ pc = Running
    /\ frontier = {}
    /\ marked' = marked
    /\ frontier' = frontier
    /\ pc' = Done

Next == Step \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Reachability definitions used in invariants
-----------------------------------------------------------------*)
ReachableFrom(v) ==
    LET Rec == RECURSIVE Rec(_)
    IN Rec(v) == {v} \cup UNION {Succ[w] : w \in Rec(v)}
    
Reachable == ReachableFrom(Root)

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
Inv1 ==
    \A n \in marked :
        Succ[n] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup frontier) = Reachable

Inv3 ==
    Reachable = marked \cup ReachableFromSet(frontier)

(* ReachableFromSet collects all nodes reachable from any node in S *)
ReachableFromSet(S) ==
    UNION {ReachableFrom(n) : n \in S}

PartialCorrectness ==
    pc = Done => marked = Reachable

=============================================================================