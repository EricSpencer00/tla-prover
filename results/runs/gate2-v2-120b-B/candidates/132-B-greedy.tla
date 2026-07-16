---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including zero). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Sequences of elements from S whose length is between 0 and bound inclusive. *)
BoundedSeq(S) == { s \in [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The Majority module is assumed to define the following: *)
(*   - Init: the initial state predicate *)
(*   - Next: the next-state relation *)
(*   - Inv: an invariant that should hold in every reachable state *)
(*   - Termination: a predicate indicating when the algorithm has finished *)
(*   - Result: a function that extracts the majority element from the state *)
(*   - Majority: a predicate that asserts the extracted element is indeed a majority *)
(*   - NoMajority: a predicate that asserts no element appears more than half the time *)
(*   - NoMajorityResult: a predicate that asserts the algorithm reports no majority *)
(*   - NoMajorityResultIsNone: a predicate that asserts the reported result is NONE when there is no majority *)

(* We expose the definitions from Majority so they can be used directly. *)
Init == Majority!Init
Next == Majority!Next
Inv == Majority!Inv
Termination == Majority!Termination
Result == Majority!Result
MajorityPred == Majority!Majority
NoMajority == Majority!NoMajority
NoMajorityResult == Majority!NoMajorityResult
NoMajorityResultIsNone == Majority!NoMajorityResultIsNone

(* The overall specification combines the initialization, the step relation, and the termination condition. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>> /\ Termination

=============================================================================