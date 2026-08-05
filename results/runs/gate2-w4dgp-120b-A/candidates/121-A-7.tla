---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES input, length, failureFn, matchIdx, loopCounter, bestOffset, pc

vars == <<input, length, failureFn, matchIdx, loopCounter, bestOffset, pc>>

Undefined == 99

IsGreater(i, j) == input[(i % length) + 1] > input[(j % length) + 1]
IsLess(i, j) == input[(i % length) + 1] < input[(j % length) + 1]
IsEqual(i, j) == input[(i % length) + 1] = input[(j % length) + 1]

StringCorpus == UNION { { Sequence(s) } : n \in 0 .. 2, s \in [1 .. n -> CharacterSet] }

Init ==
  /\ input \in StringCorpus
  /\ length = Len(input)
  /\ failureFn = [i \in 0 .. 2 * length |-> Undefined]
  /\ matchIdx = Undefined
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerLoop"

OuterStep ==
  /\ pc = "outerLoop"
  /\ loopCounter < 2 * length
  /\ pc' = "failureLookup"
  /\ UNCHANGED <<input, length, failureFn, matchIdx, loopCounter, bestOffset>>

LookupStep ==
  /\ pc = "failureLookup"
  /\ matchIdx' = failureFn[(loopCounter + bestOffset) % length]
  /\ pc' = "compareInner"
  /\ UNCHANGED <<input, length, failureFn, loopCounter, bestOffset>>

CompareStep ==
  /\ pc = "compareInner"
  /\ ~IsEqual(loopCounter, bestOffset)
  /\ matchIdx # Undefined
  /\ pc' = "compareInner"
  /\ UNCHANGED <<input, length, failureFn, matchIdx, loopCounter, bestOffset>>

OffsetStep ==
  /\ pc = "compareInner"
  /\ ~IsEqual(loopCounter, bestOffset)
  /\ IsLess(loopCounter, bestOffset)
  /\ matchIdx # Undefined
  /\ bestOffset' = loopCounter
  /\ UNCHANGED <<input, length, failureFn, matchIdx, loopCounter, pc>>

FollowStep ==
  /\ pc = "compareInner"
  /\ matchIdx # Undefined
  /\ matchIdx' = failureFn[matchIdx]
  /\ UNCHANGED <<input, length, failureFn, loopCounter, bestOffset, pc>>

PostStep ==
  /\ pc = "compareInner"
  /\ (IsLess(loopCounter, bestOffset) \/ matchIdx = Undefined)
  /\ bestOffset' = IF IsLess(loopCounter, bestOffset) THEN loopCounter ELSE bestOffset
  /\ failureFn' = [failureFn EXCEPT ![(loopCounter + bestOffset) % length] =
                     IF matchIdx = Undefined THEN Undefined ELSE matchIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<input, length, matchIdx, loopCounter>>

IncrementStep ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerLoop"
  /\ UNCHANGED <<input, length, failureFn, matchIdx, bestOffset>>

Terminate ==
  /\ pc = "outerLoop"
  /\ loopCounter = 2 * length
  /\ UNCHANGED vars

Stall ==
  /\ pc = "outerLoop"
  /\ loopCounter = 2 * length
  /\ UNCHANGED vars

Next ==
  \/ OuterStep
  \/ LookupStep
  \/ CompareStep
  \/ OffsetStep
  \/ FollowStep
  \/ PostStep
  \/ IncrementStep
  \/ Terminate
  \/ Stall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Terminate)

TypeInvariant ==
  /\ input \in StringCorpus
  /\ length = Len(input)
  /\ failureFn \in [0 .. 2 * length -> 0 .. (2 * length) \cup {Undefined}]
  /\ matchIdx \in 0 .. (2 * length) \cup {Undefined}
  /\ loopCounter \in 0 .. (2 * length)
  /\ bestOffset \in 0 .. (length - 1)
  /\ pc \in {"outerLoop", "failureLookup", "compareInner", "increment"}

Correctness ==
  /\ (pc = "outerLoop" /\ loopCounter = 2 * length) =>
       (\A i \in 0 .. (length - 1) : ~IsLess(i, bestOffset))
  /\ (pc = "outerLoop" /\ loopCounter = 2 * length /\ bestOffset < length)
       => (\A i \in 0 .. (length - 1) : IsEqual(i, bestOffset) => i >= bestOffset)

Termination == (pc = "outerLoop") ~> (pc = "outerLoop" /\ loopCounter = 2 * length)

TypeOK == TypeInvariant
Liveness == Termination

====