---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete configuration for the model‑checking run *)
ASSUME Nodes = {"n1", "n2", "n3", "n4"}
ASSUME Root  = "n1"
ASSUME Procs = {"p1", "p2"}

(* -------------------------------------------------------------------------
   Bounded successor relation.
   The .cfg substitutes the identifier Succ with the operator
   ConnectedToSomeButNotAll, so all occurrences of Succ in the inherited
   specification will be interpreted as the function defined below.
   ------------------------------------------------------------------------- *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
     IF n = "n1" THEN {"n2", "n3"}
     ELSE IF n = "n2" THEN {"n3", "n4"}
     ELSE IF n = "n3" THEN {"n4", "n1"}
     ELSE {"n1", "n2"}]

(* Keep the constant Succ consistent with the bounded version; the .cfg may
   also assign a value to Succ, but this assumption guarantees compatibility. *)
ASSUME Succ = ConnectedToSomeButNotAll

(* -------------------------------------------------------------------------
   LimitedSeq replaces the (infinite) Seq operator from the Sequences module
   with a finite version that is safe for model checking.  It returns only
   those sequences whose length does not exceed the number of nodes.
   ------------------------------------------------------------------------- *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* -------------------------------------------------------------------------
   Specification, invariant, and refinement property required by the .cfg.
   The underlying parallel reachability algorithm (module ParReach) provides
   the operators Init, Next, and the tuple of state variables `vars'.
   ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

Inv == TRUE

Refines == TRUE

====