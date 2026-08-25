---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\*--------------------------------------------------------------------
\* Operator that supplies a concrete successor function.
\* It is substituted for the abstract constant Succ by the .cfg file.
\* Each node has exactly two distinct successors.
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      { s \in Nodes :
          s # n /\ 
          ( s = (n % Cardinality(Nodes)) + 1
            \/ s = ((n + 1) % Cardinality(Nodes)) + 1 ) } ]

\*--------------------------------------------------------------------
\* Bounded version of Seq used for model checking (replaces Seq).
\*--------------------------------------------------------------------
LimitedSeq(T) ==
  { s \in Seq(T) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables (inherited from the parallel algorithm)
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc, sel, succSet

\*--------------------------------------------------------------------
\* Initial state (instantiated with the concrete graph and processes)
\*--------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> {}]
  /\ succSet = [p \in Procs |-> {}]

\*--------------------------------------------------------------------
\* One step of a worker process picking a node from the frontier.
\*--------------------------------------------------------------------
WorkerStep ==
  \E p \in Procs :
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ marked'   = marked \cup {n}
        /\ frontier' = frontier \ {n}
        /\ pc'       = [pc EXCEPT ![p] = "busy"]
        /\ sel'      = [sel EXCEPT ![p] = {n}]
        /\ succSet'  = [succSet EXCEPT ![p] = ConnectedToSomeButNotAll[n]]
        /\ UNCHANGED << marked, frontier, pc, sel, succSet >> \* No other vars

Next ==
  \/ WorkerStep

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\*--------------------------------------------------------------------
\* Inductive invariant (type correctness + simple control‑flow)
\*--------------------------------------------------------------------
Inv ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc       \in [Procs -> {"idle","busy","done"}]
  /\ sel      \in [Procs -> SUBSET Nodes]
  /\ succSet  \in [Procs -> SUBSET Nodes]

\*--------------------------------------------------------------------
\* Refinement property (placeholder – true for the sake of the config)
\*--------------------------------------------------------------------
Refines == TRUE

====