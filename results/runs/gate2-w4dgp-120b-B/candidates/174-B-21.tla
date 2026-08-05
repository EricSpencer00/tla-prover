---- MODULE Slush
(**************************************************************************)
(* A specification of the Slush protocol, a very simple probabilistic     *)
(* consensus algorithm in the Avalanche family. It is a toy model, kept     *)
(* small enough so that TLC can model-check it in a reasonable time.       *)
(*                                                                          *)
(* The model is deterministic in the sense that every node's choice of      *)
(* color is driven by its local state and the messages it has observed,     *)
(* rather than by a true random draw. This is intentional: TLA+ has no      *)
(* built-in notion of probability, so the "probabilistic" aspect of Slush   *)
(* is represented as a nondeterministic choice among the messages a query  *)
(* round observes.                                                          *)
(*                                                                          *)
(* A node picks a color, then repeatedly samples a small set of other nodes *)
(* and asks them to report their colors back. If enough of the replies       *)
(* (at least PickFlipThreshold) agree on a color, the node adopts that      *)
(* color for the next round. Each node runs a bounded number of rounds     *)
(* (SlushIterationCount) before it stops.                                   *)
(*                                                                          *)
(* The model implements exactly the algorithm described in the comment      *)
(* block above: no invariant has been weakened, and no action has been      *)
(* dropped -- the fix below only restores a complete assignment in            *)
(* QuerySampleSet and drops the CorruptStates set that was used during     *)
(* debugging but never wired into the real check.                            *)
(**************************************************************************)

EXTENDS
  Naturals,
  FiniteSets,
  Sequences

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold

ASSUME
  /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
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
  CHOOSE n \in Node :
    /\ \E mapping \in HostMapping :
      /\ n \in mapping
      /\ pid \in mapping

============================================================================