---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

(* This module configures the Echo spanning tree model for exhaustive model      *)
(* checking.  It uses a tiny fully-meshed graph of three nodes (a complete       *)
(* graph is the extreme case of connectivity, exercised here to keep the state   *)
(* space absolutely finite), and it inherits the full action set from the Echo    *)
(* specification it extends.  The test variant prints the graph to standard out  *)
(* when the model runs, which is harmless in a model-checking run.                *)

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES echoSrc, echoDest, parentOf, active, phase

vars == << echoSrc, echoDest, parentOf, active, phase >>

TypeOK ==
  /\ echoSrc \in [Node -> Node \cup {NoNode}]
  /\ echoDest \in [Node -> Node \cup {NoNode}]
  /\ parentOf \in [Node -> Node \cup {NoNode}]
  /\ active \subseteq Node
  /\ phase \in {"idle", "growing"}

InitializedTree ==
  /\ parentOf = [n \in Node |-> NoNode]
  /\ active = {initiator}
  /\ phase = "growing"
  /\ \A n \in Node: echoSrc[n] = NoNode /\ echoDest[n] = NoNode

\* Initiate echo messages from every currently active node to all of its
\* neighbours, according to the fully-meshed graph defined by the constant set
\* R, which here is the complete set of distinct node pairs.  Messages are
\* sampled nondeterministically (no ordering), which is exactly the point: the
\* model must explore every possible interleaving of them, not any deterministic
\* conduit ordering.
SendEchoes ==
  /\ phase = "growing"
  /\ \E src \in active:
       /\ \E dst \in (Node \ {src}):
            /\ << src, dst >> \in R
            /\ echoSrc' = [echoSrc EXCEPT ![dst] = src]
            /\ echoDest' = [echoDest EXCEPT ![dst] = src]
  /\ UNCHANGED << parentOf, active, phase >>

\* The destination adopts the echoed source as its tree parent and becomes
\* active (its own echoes fire next round); the message is then consumed.
AcceptEcho ==
  /\ \E n \in Node:
       /\ echoSrc[n] # NoNode
       /\ n \notin active
       /\ parentOf' = [parentOf EXCEPT ![n] = echoSrc[n]]
       /\ active' = active \cup {n}
       /\ echoSrc' = [echoSrc EXCEPT ![n] = NoNode]
       /\ echoDest' = [echoDest EXCEPT ![n] = NoNode]
  /\ UNCHANGED phase

DeclineEcho ==
  /\ \E n \in Node:
       /\ echoSrc[n] # NoNode
       /\ n \in active
       /\ echoSrc' = [echoSrc EXCEPT ![n] = NoNode]
       /\ echoDest' = [echoDest EXCEPT ![n] = NoNode]
  /\ UNCHANGED << parentOf, active, phase >>

\* Completion is not a termination test but an ordinary transition that rolls
\* the spanning-tree phase forward once every node has been added to it.
Complete ==
  /\ phase = "growing"
  /\ \A n \in Node: n \in active
  /\ phase' = "idle"
  /\ UNCHANGED << echoSrc, echoDest, parentOf, active >>

Next == SendEchoes \/ AcceptEcho \/ DeclineEcho \/ Complete

\* The test variant prints the graph adjacency to standard output at runtime
\* (harmless in a model-checking run) and then behaves exactly like Init.
Init ==
  /\ InitializedTree
  /\ \E out \in R: (UNCHANGED vars) /\ \* the emission is a no-op on state, but a
       PrintT("\nEmitter: " \/ out[1] \/ " -> " \/ out[2])
  /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A a, b \in Node: (a # b /\ parentOf[b] # NoNode /\ parentOf[b] = a) ~> (parentOf[a] # NoNode)
  /\ \A n \in Node: (n # initiator /\ parentOf[n] # NoNode) => (parentOf[n] # n)
  /\ \A n \in Node: (n # initiator /\ parentOf[n] # NoNode) ~> (parentOf[parentOf[n]] # NoNode)

TestSpec == Spec

====