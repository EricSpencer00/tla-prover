---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, Nat

\* Failure is the sentinel value meaning "no failure function entry".
Failure == Nat

VARIABLES inputString, length, failureFun, patIdx, outer, bestOffset, pc

vars == <<inputString, length, failureFun, patIdx, outer, bestOffset, pc>>

RECURSIVE Rotate(_)
Rotate(s) ==
  IF Len(s) = 0 THEN s
  ELSE LET k == Head(s) IN Rotate(Tail(s)) \o <<k>>

\* The corpus: all zero-indexed sequences over the character set up to the
\* maximum length permitted by the model checker.
Corpus == UNION { [1..n -> CharacterSet] : n \in 0..Nat }

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failureFun \in [0..2 * Nat -> 0..Nat]
  /\ patIdx \in 0..Nat
  /\ outer \in 1..(2 * Nat)
  /\ bestOffset \in 0..Nat
  /\ pc \in {"outerCheck", "failureLookup", "innerLoop", "postComp", "done"}

Init ==
  /\ \E s \in Corpus : inputString = s
  /\ length = Len(inputString)
  /\ failureFun = [i \in 0..2 * Nat |-> Failure]
  /\ patIdx = Failure
  /\ outer = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ outer < 2 * Nat
  /\ pc' = "failureLookup"
  /\ UNCHANGED <<inputString, length, failureFun, patIdx, outer, bestOffset>>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, length, failureFun, patIdx, outer, bestOffset>>

CharAt(i) == inputString[(i % length) + 1]

InnerLoop ==
  /\ pc = "innerLoop"
  /\ CharAt(outer) # CharAt(bestOffset + patIdx + 1)
  /\ patIdx # Failure
  /\ patIdx' = failureFun[patIdx]
  /\ pc' = IF CharAt(outer) < CharAt(bestOffset + patIdx + 1) THEN "postComp" ELSE "innerLoop"
  /\ UNCHANGED <<inputString, length, failureFun, outer, bestOffset>>

PostComparison ==
  /\ pc = "postComp"
  /\ IF CharAt(outer) # CharAt(bestOffset + patIdx + 1) /\ patIdx = Failure
     THEN bestOffset' = IF CharAt(outer) < CharAt(bestOffset + patIdx + 1) THEN outer % length ELSE bestOffset
     ELSE bestOffset' = bestOffset
  /\ failureFun' = [failureFun EXCEPT ![patIdx] = IF patIdx = Failure THEN Failure ELSE patIdx + 1]
  /\ patIdx' = Failure
  /\ outer' = outer + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED inputString

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Done ==
  /\ pc = "outerCheck"
  /\ outer >= 2 * Nat
  /\ pc' = "done"
  /\ UNCHANGED <<inputString, length, failureFun, patIdx, outer, bestOffset>>

Next ==
  \/ OuterCheck \/ FailureLookup \/ InnerLoop \/ PostComparison \/ Done \/ Stall

\* A rotation of the input string by shift positions.
RotateBy(shift) == Rotate(SubSeq(inputString, shift + 1, length) \o SubSeq(inputString, 1, shift))

AtLeastAsSmallAsAll ==
  \A i \in 0..(length - 1) :
    RotateBy(bestOffset) <= RotateBy(i) /\ (RotateBy(bestOffset) = RotateBy(i) => bestOffset <= i)

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Done)

Correctness == AtLeastAsSmallAsAll

====