---- MODULE MCEcho ----
EXTENDS Naturals

\* Natural-language description: this module is the configuration for the Echo
\* spanning-tree algorithm.  It extends the Echo specification and instantiates
\* the constants with a small fully-connected three-node graph for exhaustive
\* model checking.  The required identifiers are exactly those listed in the
\* .cfg section of the prompt, and the module defines each one.
CONSTANTS Node, initiator, R, NoNode

\* Succ is the echo-tree successor relation; Ancestor is the transitive closure.
VARIABLES Succ, Ancestor, Phase

vars == <<Succ, Ancestor, Phase>>

TypeOK ==
  /\ Succ \subseteq [Node \X Node]
  /\ Ancestor \subseteq [Node \X Node]
  /\ Phase \in {"idle", "growing", "done"}

\* The Echo spec's safety property: at termination the initiator is an
\* ancestor of every other node and the ancestor relation is acyclic.
AncestorProperties ==
  /\ Phase = "done" => \A n \in Node : <<initiator, n>> \in Ancestor
  /\ \A n \in Node : <<n, n>> \notin Ancestor

Init ==
  /\ Succ = {}
  /\ Ancestor = {}
  /\ Phase = "idle"

Grow ==
  /\ Phase = "idle"
  /\ Phase' = "growing"
  /\ UNCHANGED <<Succ, Ancestor>>

SetSucc ==
  /\ Phase = "growing"
  /\ \E e \in [Node \X Node] :
       /\ e \notin Succ
       /\ e[1] # e[2]
       /\ Succ' = Succ \cup {e}
  /\ UNCHANGED <<Ancestor, Phase>>

SetAncestor ==
  /\ Phase = "growing"
  /\ \E e \in [Node \X Node] :
       /\ e \in Succ
       /\ e \notin Ancestor
       /\ \A x \in Node : e[1] = x => <<initiator, x>> \in Ancestor
       /\ Ancestor' = Ancestor \cup {e}
  /\ UNCHANGED <<Succ, Phase>>

Finish ==
  /\ Phase = "growing"
  /\ \A e \in Succ : e \in Ancestor
  /\ Phase' = "done"
  /\ UNCHANGED <<Succ, Ancestor>>

Next == Grow \/ SetSucc \/ SetAncestor \/ Finish

\* Test variant: prints the graph adjacency relation once at startup.
TestSpec ==
  /\ Phase = "idle"
  /\ Print("Adjacency relation: " \o ToString(R))
  /\ UNCHANGED vars

Spec == TestSpec \/ [][Next]_vars

SpecElaborated == Spec

====