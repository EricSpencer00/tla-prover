---- MODULE MCReachable ----
EXTENDS Reachable, Sequences

(* Each node is connected to a non‑empty proper subset of the nodes.
   This deterministic definition satisfies the “some but not all”
   intent while avoiding the costly CHOOSE over a huge function space,
   thus preventing the stack overflow during model checking. *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> Nodes \ {n}]

(* Returns the set of all sequences over S whose length does not exceed
   the number of nodes.  This uses the standard Seq and Len operators
   from the Sequences module, preserving the intended semantics of the
   original definition. *)
LimitedSeq(S) ==
  { seq \in Seq(S) : Len(seq) \in 0 .. Cardinality(Nodes) }

====