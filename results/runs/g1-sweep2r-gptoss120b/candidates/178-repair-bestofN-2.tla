---- MODULE SpanTreeRandom ----
(***************************************************************************)
(* The specification in this module is a modified version of the one in    *)
(* module SpanTree obtained by replacing the declared constant Edges with  *)
(* a defined constant that equals a randomly chosen set of edges joining   *)
(* the nodes in Nodes.  Thus it can be used to test the algorithm of       *)
(* SpanTree on a randomly chosen node, making it easy to check the         *)
(* algorithm on a sequence of different graphs.                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root, MaxCardinality

Edges == 
  UNION { {{n, m} : m \in RandomElement(SUBSET (Nodes\{n}))} : n \in Nodes }
  (*************************************************************************)
  (* To understand this definition let's look at its subformulas, from the *)
  (* inside out.                                                           *)
  (*                                                                       *)
  (*  - SUBSET (Nodes \ {n})  is the set of all subsets of the set         *)
  (*    Nodes \ {n} , which is the set of all nodes other than n.          *)
  (*                                                                       *)
  (*  - RandomElement(...)  is a hack introduced in the TLC module.  TLC   *)
  (*    computes its value to be a randomly chosen element in the set      *)
  (*    ... . This is hack because, in math, an expression has the same    *)
  (*    value whenever it's computed.  The value of 2^{1/2} is the same    *)
  (*    next Thursday as it is today.  Every mathematical expression exp   *)
  (*    satisfies exp = exp.  However, TLC may evaluate                    *)
  (*                                                                       *)
  (*       RandomElement(S) = RandomElement(S)                             *)
  (*                                                                       *)
  (*    to equal FALSE if S is a set with more than 1 element, This is     *)
  (*    one of the few cases in which TLC does not obey the rules of math. *)
  (*                                                                       *)
  (*  - {{n, m} : m \in RandomElement(...)}  is the set of  elements that  *)
  (*    equal the set {n, m} for m some element of RandomElement(...) .    *)
  (*                                                                       *)
  (*  - UNION { ... : n \in Nodes }  is the union of all sets ...  for n   *)
  (*    an element of Nodes.  This expression makes sense if the           *)
  (*    expression equals a set that depends on the value of n.            *)
  (*************************************************************************)

ASSUME /\ Root \in Nodes
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)
       
VARIABLES mom, dist
vars == <<mom, dist>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]
          /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        
(* 
   The original Next action tries to improve the distance of a node n
   by picking a neighbour m whose distance is strictly smaller and then
   setting dist[n] to an intermediate value d between dist[m]+1 and
   dist[n]-1.  This can get stuck when a node's distance is only one
   larger than that of a neighbour (gap = 1) but the mother relation
   has not yet been updated to reflect the correct parent.  To guarantee
   progress we add a second disjunct that directly sets dist[n] to the
   optimal value dist[m]+1 whenever such a gap exists.
*)
Next == 
  \/ \E n \in Nodes :
        \E m \in Nbrs(n) :
           /\ dist[m] < 1 + dist[n]
           /\ \E d \in (dist[m]+1) .. (dist[n] - 1) :
                /\ dist' = [dist EXCEPT ![n] = d]
                /\ mom'  = [mom  EXCEPT ![n] = m]
  \/ \E n \in Nodes :
        \E m \in Nbrs(n) :
           /\ dist[m] + 1 < dist[n]            \* there is a gap of at least 2
           /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
           /\ mom'  = mom                       \* keep the current mother

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
-----------------------------------------------------------------------------
PostCondition == 
  \A n \in Nodes :
    \/ /\ n = Root 
       /\ dist[n] = 0
       /\ mom[n] = n
    \/ /\ dist[n] = MaxCardinality 
       /\ mom[n] = n
       /\ \A m \in Nbrs(n) : dist[m] = MaxCardinality
    \/ /\ dist[n] \in 1..(MaxCardinality-1)
       /\ mom[n] \in Nbrs(n)
       /\ dist[n] = dist[mom[n]] + 1

Safety == []((~ ENABLED Next) => PostCondition)

Liveness == <>PostCondition
(***************************************************************************)
(* Model Model_1 has TLC check these correctness condition for a (randomly *)
(* chosen) graph with six nodes.  On a few tries, it took TLC an average   *)
(* of a little more than 30 seconds to do it.                              *)
(***************************************************************************)
=============================================================================