---- MODULE Slush ----------------------------------------------------------------
(**************************************************************************)
(* A specification of the Slush protocol, an extremely simple,           *)
(* probabilistic consensus algorithm in the Avalanche family.  TLA⁺ has   *)
(* no native probabilistic modeling capabilities, so this spec is         *)
(* primarily executable pseudocode.  It cannot, for example, answer       *)
(* "what is the maximum probability of not converging with N iterations?" *)
(* Such questions are answered in a language like PRISM, but PRISM is      *)
(* difficult to get running on this problem.                              *)
(**************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
       /\ SlushIterationCount \in Nat
       /\ SampleSetSize \in Nat
       /\ PickFlipThreshold \in Nat

ASSUME HostMappingType ==
  /\ Cardinality(Node) = Cardinality(HostMapping)
  /\ \A mapping \in HostMapping :
       /\ Cardinality(mapping) = 3
       /\ \E e \in mapping : e \in Node
       /\ \E e \in mapping : e \in SlushLoopProcess
       /\ \E e \in mapping : e \in SlushQueryProcess

HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node : \E mapping \in HostMapping : n \in mapping /\ pid \in mapping

=============================================================================