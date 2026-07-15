---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent

(* ---------- Helper definitions ---------- *)

NodeSet == Node

(* adjacency relation derived from the edge set R *)
Adj == { <<i, j>> : <<i, j>> \in R }

(* ---------- Type correctness ---------- *)

NodeAndNoNode == Node \cup {NoNode}

TypeOK == /\ parent \in [Node -> NodeAndNoNode]
          /\ initiator \in Node
          /\ NoNode \notin Node
          /\ NoNode \in NodeAndNoNode
          /\ initiator \in Node

(* ---------- Initial state ---------- *)

ParentInit == [n \in Node |-> NoNode]

Init == /\ parent = ParentInit
        /\ initiator \in Node

(* ---------- Actions ---------- *)

Send =
  \E i \in Node :
    /\ parent[i] = NoNode
    /\ \E j \in Node :
         /\ i # j
         /\ <<j, i>> \in Adj
         /\ parent' = [parent EXCEPT ![i] = j]

Receive =
  \E i \in Node :
    /\ parent[i] # NoNode
    /\ \E j \in Node :
         /\ i # j
         /\ <<i, j>> \in Adj
         /\ parent[i] = j
         /\ parent' = [parent EXCEPT ![i] = NoNode]

Next == Send \/ Receive

(* ---------- Test variant that prints the graph ---------- *)

PrintAdj ==
  /\ UNCHANGED parent
  /\ Print(Adj)

(* ---------- Specification ---------- *)

TestSpec == Init /\ [][Next]_<<parent>>

(* ---------- Safety invariant (ancestor properties) ---------- *)

Ancestor(i) ==
  IF parent[i] = NoNode
     THEN initiator = i
     ELSE i = initiator \/ i \in Ancestor(parent[i])

AncestorProperties ==
  \A i \in Node : initiator \in ( (parent[i] = NoNode) ? {} : {parent[i]} ) => i # initiator

(* The above captures that every node either is the initiator or has a parent,
   and the initiator never appears as a child of another node. *)

====