---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*-----------------------------------------------------------------
  Type definition
-----------------------------------------------------------------*)
Node == Nodes

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Initial state (as required by the algorithm)
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(*-----------------------------------------------------------------
  Actions (algorithmic steps) – only those needed for the invariants
-----------------------------------------------------------------*)
Step ==
    \/ /\ pc = "Init"
       /\ pc' = "Mark"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Mark"
       /\ marked' = marked \cup frontier
       /\ frontier' = {}
       /\ pc' = "Done"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next == Step

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Reachability definitions used in the invariants
-----------------------------------------------------------------*)
ReachableFrom(S) ==
    { n \in Node : 
        \E p \in Seq(Node) :
            Len(p) > 0 /\ Head(p) = Root /\ Last(p) = n /\ 
            \A i \in 1..(Len(p)-1) : p[i] \in S /\ p[i+1] \in S }

(* Invariant 1: type correctness + successor property (inductive) *)
Inv1 ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ \A n \in marked : \A s \in Node :
          ( <<n, s>> \in Edge \/ <<s, n>> \in Edge ) =>
          (s \in marked \/ s \in frontier)

(* Assume Edge is defined in the extended algorithm module; for
   this standalone specification we introduce a placeholder. *)
CONSTANT Edge

(* Invariant 2: lemma‑derived equivalence *)
Inv2 ==
    marked \cup ReachableFrom(frontier) =
    ReachableFrom(marked \cup frontier)

(* Invariant 3: final correctness condition *)
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(*-----------------------------------------------------------------
  Theorem (partial correctness)
-----------------------------------------------------------------*)
THEOREM PartialCorrectness ==
    Spec => []((pc = "Done") => marked = ReachableFrom({Root}))

=============================================================================