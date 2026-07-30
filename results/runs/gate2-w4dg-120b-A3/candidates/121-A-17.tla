---- MODULE LeastCircularSubstring ----
EXTENDS FiniteSets, Naturals, Sequences

\* The config file replaces the standard Nat operator from Naturals with a
\* finite version derived from the character set, so Nat is never declared
\* here and the model stays within a finite bound.
\*   [ZSequences]CharacterSet
\* The character set is a constant, so the FiniteNat it defines is finite.
CONSTANT CharacterSet

MaxStringLength == 2
Successor(x) == (x + 1) % 2
Sentinel == MaxStringLength

VARIABLES inputString, length, failure, patternIdx, loopCounter, bestOffset, pc

vars == <<inputString, length, failure, patternIdx, loopCounter, bestOffset, pc>>

StringUniverse == Seq(CharacterSet)

\* The spec explores every string in the universe, up to the model's bound.
Corpus == {s \in StringUniverse : Len(s) <= MaxStringLength}

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure \in [0 .. 2 * MaxStringLength -> 0 .. Sentinel]
  /\ patternIdx \in 0 .. Sentinel
  /\ loopCounter \in 1 .. 2 * MaxStringLength
  /\ bestOffset \in 0 .. (IF length = 0 THEN 0 ELSE length - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "compareLess",
             "followChain", "postCompare", "increment", "done"}

Init ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure = [i \in 0 .. 2 * MaxStringLength |-> Sentinel]
  /\ patternIdx = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

\* Outer loop: process the doubled string, which handles the wrap-around.
OuterCheck ==
  /\ pc = "outerCheck"
  /\ pc' = IF loopCounter < 2 * MaxStringLength THEN "lookup" ELSE "done"
  /\ UNCHANGED <<inputString, length, failure, patternIdx, loopCounter,
                 bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ patternIdx' = failure[Successor(bestOffset + (loopCounter % length))]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ patternIdx # Sentinel
  /\ \A i \in 0 .. (Sentinel - 1) : ~(failure[i] = patternIdx)
  /\ characterAt(i) /= characterAt(distance + i)
  /\ pc' = "compareLess"
  /\ UNCHANGED <<inputString, length, failure, patternIdx, loopCounter,
                 bestOffset>>

CompareLess ==
  /\ pc = "compareLess"
  /\ bestOffset' = IF characterAt(0) < characterAt(distance) THEN loopCounter % length
                   ELSE bestOffset
  /\ patternIdx' = failure[patternIdx]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, length, failure, loopCounter>>

FollowChain ==
  /\ pc = "innerLoop"
  /\ patternIdx # Sentinel
  /\ patternIdx' = failure[patternIdx]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

\* After the inner loop, a character mismatch that did not follow a chain
\* is handled here: the failure function is reset or extended.
PostCompare ==
  /\ pc = "innerLoop"
  /\ patternIdx = Sentinel
  /\ characterAt(0) /= characterAt(distance)
  /\ IF characterAt(0) < characterAt(distance)
     THEN bestOffset' = loopCounter % length
     ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![Successor(bestOffset + (loopCounter % length))] =
                   IF patternIdx = Sentinel THEN Sentinel ELSE patternIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, length, patternIdx, loopCounter>>

Increment ==
  /\ pc \in {"increment", "postCompare"}
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, length, failure, patternIdx, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ InnerLoop \/ CompareLess
  \/ FollowChain \/ PostCompare \/ Increment \/ Done

Spec == Init /\ [][Next]_vars
        /\ WF_vars(OuterCheck) /\ WF_vars(Lookup) /\ WF_vars(InnerLoop)
        /\ WF_vars(CompareLess) /\ WF_vars(FollowChain)
        /\ WF_vars(PostCompare) /\ WF_vars(Increment)

\* A rotation is lexicographically no greater than any other rotation.
RotationsAreOrdered ==
  \A i \in 0 .. length - 1 :
    \A j \in 0 .. length - 1 :
      LET seq(k) == inputString[((bestOffset + k) % length) + 1]
          base(k) == inputString[((i + k) % length) + 1]
          firstDiff == CHOOSE m \in 0 .. length - 1 : seq(m) # base(m)
      IN IF seq(firstDiff) > base(firstDiff) THEN FALSE ELSE TRUE

Correctness == (pc = "done") => RotationsAreOrdered

Termination == <>(pc = "done")

\* The config file replaces this operator with the character set; it is
\* defined here because the module expects it to exist.
[ZSequences]CharacterSet == CharacterSet

characterAt(i) ==
  inputString[((bestOffset + i) % length) + 1]

distance == Successor(loopCounter % length)

====