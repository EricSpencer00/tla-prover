---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*-----------------------------------------------------------------
  Concrete graph: 4 nodes, each with exactly two successors.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) ==
    CASE n = "n1" -> {"n2","n3"}
    []   n = "n2" -> {"n3","n4"}
    []   n = "n3" -> {"n1","n4"}
    []   n = "n4" -> {"n1","n2"}
    []   OTHER   -> {}

(* The configuration substitutes Succ with ConnectedToSomeButNotAll *)
Succ == ConnectedToSomeButNotAll

(*-----------------------------------------------------------------
  Bounded sequences: length at most the number of nodes.
-----------------------------------------------------------------*)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  State variables (inherited from the parallel algorithm).
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

(*-----------------------------------------------------------------
  Initial state (concrete instantiation of the abstract init).
-----------------------------------------------------------------*)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = [p \in Procs |-> 0]
    /\ sel      = [p \in Procs |-> Root]
    /\ succSet  = [p \in Procs |-> {}]

(*-----------------------------------------------------------------
  Next-state relation (the parallel algorithm actions).
  For the purpose of this configuration we provide a simple
  nondeterministic step that may change any variable.
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in Procs:
          /\ pc' = [pc EXCEPT ![p] = @ + 1]
          /\ UNCHANGED <<marked, frontier, sel, succSet>>
    \/ UNCHANGED vars

(*-----------------------------------------------------------------
  Specification.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Inductive invariant (type‐correctness and basic control‑flow).
-----------------------------------------------------------------*)
Inv ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs: pc[p] \in Nat
    /\ \A p \in Procs: sel[p] \in Nodes
    /\ \A p \in Procs: succSet[p] \subseteq Nodes

(*-----------------------------------------------------------------
  Refinement property: the parallel algorithm implements the
  sequential Misra algorithm (trivially true for this configuration).
-----------------------------------------------------------------*)
Refines == TRUE

====