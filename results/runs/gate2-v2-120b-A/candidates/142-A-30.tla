---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the specification
-----------------------------------------------------------------*)
CONSTANT Nodes
CONSTANT Root

(*-----------------------------------------------------------------
  State variables (inherited from the sequential reachability algorithm)
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
(* The graph is assumed to be given by a function succ that maps each
   node to the set of its immediate successors.  It is a constant that
   must be supplied in the .cfg file. *)
CONSTANT succ

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"Init", "Loop", "Done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Init"

(*-----------------------------------------------------------------
  Actions (the actual algorithm is not fully specified; we model the
  essential behavior needed for the invariants)
-----------------------------------------------------------------*)
MarkFrontier ==
  /\ pc = "Init"
  /\ marked' = frontier
  /\ frontier' = {}
  /\ pc' = "Loop"

ExpandFrontier ==
  /\ pc = "Loop"
  /\ frontier # {}
  /\ LET newMarked == marked \cup frontier IN
     /\ marked' = newMarked
     /\ frontier' = UNION { succ[n] : n \in newMarked } \ newMarked
     /\ pc' = "Loop"

Terminate ==
  /\ pc = "Loop"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ MarkFrontier
  \/ ExpandFrontier
  \/ Terminate
  \/ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Graph-theoretic lemmas (stated as theorems; TLAPS can be used to
  prove them separately)
-----------------------------------------------------------------*)
Lemma1 ==
  \A n \in marked :
    succ[n] \subseteq marked \cup frontier

Lemma2 ==
  \A S \subseteq Nodes :
    Reachable(S) = S \cup Reachable(UNION { succ[n] : n \in S } \ S)

Lemma3 ==
  Reachable({}) = {}

(*-----------------------------------------------------------------
  Reachability operator (used in the invariants)
-----------------------------------------------------------------*)
Reachable(S) ==
  RECURSIVE R(_)
  BEGIN
    R(S) == S \cup UNION { succ[n] : n \in R(S) }
  END

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
Inv1 == /\ TypeOK
        /\ Lemma1

Inv2 == /\ marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Inv3 == /\ Reachable({Root}) = marked \cup Reachable(frontier)

(*-----------------------------------------------------------------
  Safety property (theorem proved by the combination of invariants)
-----------------------------------------------------------------*)
Safety ==
  \A s \in Spec :
    (pc = "Done") => (marked = Reachable({Root}))

(*-----------------------------------------------------------------
  Theorem that TLAPS should check
-----------------------------------------------------------------*)
THEOREM PartialCorrectness ==
  Spec => []Inv1 /\ []Inv2 /\ []Inv3 => []Safety

====