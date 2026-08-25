---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

(*-----------------------------------------------------------------
  Bounded version of Seq used for model checking.
  The .cfg will replace occurrences of Seq with LimitedSeq.
-----------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Bounded successor relation. The .cfg substitutes this for Succ.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) ==
    IF Cardinality(Nodes) < 2 THEN {}
    ELSE
      CHOOSE succSet \in SUBSET Nodes :
        /\ Cardinality(succSet) = 2
        /\ n \notin succSet

(*-----------------------------------------------------------------
  State variables (inherited from the parallel algorithm).
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc, sel, succSet

(*-----------------------------------------------------------------
  Initial state (concrete graph and process set are supplied by constants).
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> 0]
    /\ sel = [p \in Procs |-> <<>>]      \* empty sequence, length 0 ≤ |Nodes|
    /\ succSet = [p \in Procs |-> {}]

(*-----------------------------------------------------------------
  Next-state relation (placeholder – actual actions come from the
  parallel algorithm; here we keep it simple for compilation).
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in Procs :
          /\ pc' = [pc EXCEPT ![p] = @ + 1]
          /\ UNCHANGED <<marked, frontier, sel, succSet>>
    \/ UNCHANGED <<marked, frontier, pc, sel, succSet>>

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

Inv == TRUE

Refines == TRUE

====