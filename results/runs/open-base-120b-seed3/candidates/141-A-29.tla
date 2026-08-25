---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*---------------------------------------------------*)
(*  Constants required by the .cfg file                *)
CONSTANTS Nodes, Root, Succ

(*---------------------------------------------------*)
(*  Operator that the .cfg substitutes for Succ        *)
ConnectedToSomeButNotAll == [n \in Nodes |-> {}]

(*---------------------------------------------------*)
(*  Limited version of Seq (replaces Seq)             *)
LimitedSeq(S) == Seq(S)

(*---------------------------------------------------*)
(*  State variables                                    *)
VARIABLES marked, frontier, pc

(*---------------------------------------------------*)
(*  Reachability definition using transitive closure  *)
Rel == UNION { {<<n, m>>} : n \in Nodes, m \in Succ[n] }

Reach(S) == { y \in Nodes : \E x \in S : <<x, y>> \in TC(Rel) }

(*---------------------------------------------------*)
(*  Type correctness invariant                        *)
TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"Run", "Done"}

(*---------------------------------------------------*)
(*  Invariant 1: successors of marked nodes are in     *)
(*  marked or frontier                                 *)
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

(*---------------------------------------------------*)
(*  Invariant 2: union of marked and reachable from    *)
(*  frontier equals reachable from their union        *)
Inv2 == (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

(*---------------------------------------------------*)
(*  Invariant 3: reachable from Root equals marked     *)
(*  plus nodes reachable from frontier                *)
Inv3 == Reach({Root}) = marked \cup Reach(frontier)

(*---------------------------------------------------*)
(*  Partial correctness: when terminated, marked set *)
(*  equals the set of nodes reachable from Root       *)
PartialCorrectness == (pc = "Done") => (marked = Reach({Root}))

(*---------------------------------------------------*)
(*  Initial state                                      *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

(*---------------------------------------------------*)
(*  Main action: pick a node from frontier            *)
Main ==
  /\ pc = "Run"
  /\ frontier # {}
  /\ \E n \in frontier :
        IF n \notin marked THEN
           /\ marked'   = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        ELSE
           /\ marked'   = marked
           /\ frontier' = frontier \ {n}
        /\ pc' = "Run"

(*---------------------------------------------------*)
(*  Termination step: frontier empty                  *)
Terminate ==
  /\ pc = "Run"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

(*---------------------------------------------------*)
(*  Stutter after termination                          *)
DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<marked, frontier, pc>>

(*---------------------------------------------------*)
(*  Next-state relation                                *)
Next == Main \/ Terminate \/ DoneStutter

(*---------------------------------------------------*)
(*  Specification                                      *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Next)

(*---------------------------------------------------*)
(*  Liveness property: eventual termination            *)
Termination == <> (pc = "Done")

====