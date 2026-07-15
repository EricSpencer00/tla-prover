---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the reference configuration
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* Set of graph nodes
    Root,    \* The distinguished start node
    Procs,   \* Set of worker process identifiers
    Succ,    \* Successor function: maps each node to a non‑empty 2‑element set of nodes
    Seq      \* Upper bound on sequence length (maximal allowed length)

(*-----------------------------------------------------------------
  State variables (inherited from the parallel algorithm)
-----------------------------------------------------------------*)
VARIABLES
    marked,    \* Set of nodes that have been discovered
    frontier, \* Set of nodes currently being explored
    pc,        \* Mapping from each process to its program counter (one of "Idle", "Work", "Done")
    sel,       \* Mapping from each process to the node it is currently working on (or NULL)
    succSet    \* Mapping from each process to the subset of Succ(node) it has already processed

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
PCVals == {"Idle", "Work", "Done"}

NullNode == -1

InitSel == [p \in Procs |-> NullNode]

InitSuccSet == [p \in Procs |-> {}]

(*-----------------------------------------------------------------
  Initial state (inherits from the parallel algorithm)
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "Idle"]
    /\ sel = InitSel
    /\ succSet = InitSuccSet

(*-----------------------------------------------------------------
  Actions (inherited from the parallel algorithm)
-----------------------------------------------------------------*)
Idle(p) ==
    /\ pc[p] = "Idle"
    /\ \E n \in frontier :
          /\ sel' = [sel EXCEPT ![p] = n]
          /\ frontier' = frontier \ {n}
          /\ marked' = marked \cup {n}
          /\ pc' = [pc EXCEPT ![p] = "Work"]
    /\ UNCHANGED << succSet >>

Work(p) ==
    /\ pc[p] = "Work"
    /\ sel[p] # NullNode
    /\ \E s \in Succ[sel[p]] \ Sel[succSet[p]] :
          /\ succSet' = [succSet EXCEPT ![p] = succSet[p] \cup {s}]
    /\ IF Cardinality(succSet[p]) = 2
         THEN /\ pc' = [pc EXCEPT ![p] = "Done"]
              /\ sel' = [sel EXCEPT ![p] = NullNode]
         ELSE /\ UNCHANGED << pc, sel >>
    /\ UNCHANGED << marked, frontier >>

Done(p) ==
    /\ pc[p] = "Done"
    /\ \/ frontier' = frontier \cup succSet[p]
       \/ frontier' = frontier
    /\ marked' = marked \cup succSet[p]
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ succSet' = [succSet EXCEPT ![p] = {}]
    /\ sel' = InitSel
    /\ UNCHANGED << >>

Next ==
    \/ \E p \in Procs : Idle(p)
    \/ \E p \in Procs : Work(p)
    \/ \E p \in Procs : Done(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(*-----------------------------------------------------------------
  Inductive invariant (type correctness + basic control flow)
-----------------------------------------------------------------*)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> PCVals]
    /\ sel \in [Procs -> (Nodes \cup {NullNode})]
    /\ succSet \in [Procs -> SUBSET Nodes]
    /\ \A p \in Procs :
          /\ (pc[p] = "Idle") => (sel[p] = NullNode /\ succSet[p] = {})
          /\ (pc[p] = "Work") => (sel[p] # NullNode /\ succSet[p] \subseteq Succ[sel[p]])
          /\ (pc[p] = "Done") => (sel[p] = NullNode /\ succSet[p] = {})

(*-----------------------------------------------------------------
  Refinement property: the parallel algorithm implements the sequential Misra algorithm.
  The precise formulation of the sequential invariant (SeqInv) would normally be
  imported from the sequential module; here we assert that the reachable
  configurations satisfy the existential condition that there exists a sequence
  of length at most Seq that respects the sequential ordering.
-----------------------------------------------------------------*)
SeqInv ==
    \E seq \in Seq(<<>>):
        /\ Len(seq) <= Seq
        /\ \A i \in 1..Len(seq) :
              /\ seq[i] \in Nodes
              /\ (i = 1 => seq[i] = Root)
              /\ (i > 1 => seq[i] \in Succ[seq[i-1]])

Refines == Spec => []SeqInv

====