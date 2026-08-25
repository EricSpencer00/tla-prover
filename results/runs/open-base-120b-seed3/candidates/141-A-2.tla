---- MODULE Reachable ----
EXTENDS Sequences, FiniteSets, TLC

CONSTANTS
    Nodes,   \* the set of all graph nodes
    Root,    \* a distinguished node in Nodes
    Succ     \* a function mapping each node to the set of its successors

(* ------------------------------------------------------------------- *)
(*  Operators required by the configuration                           *)
(* ------------------------------------------------------------------- *)

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == Seq(S)

(* ------------------------------------------------------------------- *)
(*  Helper definitions                                                *)
(* ------------------------------------------------------------------- *)

\* Relation induced by the successor function
Rel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

\* Nodes reachable from a given node (including the node itself)
ReachFrom(n) == { m \in Nodes : <<n, m>> \in TC(Rel) } \cup {n}

\* Nodes reachable from a set of nodes
Reach(S) == UNION { ReachFrom(n) : n \in S }

(* ------------------------------------------------------------------- *)
(*  Variables                                                         *)
(* ------------------------------------------------------------------- *)

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(* ------------------------------------------------------------------- *)
(*  Initialization                                                    *)
(* ------------------------------------------------------------------- *)

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

(* ------------------------------------------------------------------- *)
(*  Next-state relation                                               *)
(* ------------------------------------------------------------------- *)

Next ==
    \/ /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ frontier # {}
       /\ \E n \in frontier:
            /\ IF n \notin marked
                 THEN /\ marked' = marked \cup {n}
                      /\ frontier' = frontier \cup Succ[n]
                 ELSE /\ marked' = marked
                      /\ frontier' = frontier \ {n}
            /\ pc' = pc
            /\ UNCHANGED <<marked, frontier>> \except [marked = marked', frontier = frontier']

(* ------------------------------------------------------------------- *)
(*  Specification                                                     *)
(* ------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ------------------------------------------------------------------- *)
(*  Type correctness invariant                                        *)
(* ------------------------------------------------------------------- *)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

(* ------------------------------------------------------------------- *)
(*  Safety invariants                                                 *)
(* ------------------------------------------------------------------- *)

Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == (frontier = {} => marked = Reach({Root}))

(* ------------------------------------------------------------------- *)
(*  Liveness property                                                 *)
(* ------------------------------------------------------------------- *)

Termination == <> (frontier = {})

(* ------------------------------------------------------------------- *)
(*  Theorems (optional, for readability)                              *)
(* ------------------------------------------------------------------- *)

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====