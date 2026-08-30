---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Zero-indexed version of the standard Sequences [i \in Nat |-> i \in 1..n].
\* Becomes the standard definition when Nat is replaced by Naturals.Nat
\* in the .cfg file, which is exactly what keeps the model finite.
Indices == 0..(Len(<< >>) - 1)

VARIABLES inputString, strLen, failure, matchIdx, loopCounter, bestOffset, pc

vars == << inputString, strLen, failure, matchIdx, loopCounter, bestOffset, pc >>

Sentinel == 999

TypeInvariant ==
  /\ inputString \in [Indices -> CharacterSet]
  /\ strLen = Len(inputString)
  /\ failure \in [Indices -> (Indices \cup {Sentinel})]
  /\ matchIdx \in (Indices \cup {Sentinel})
  /\ loopCounter \in 1..(strLen * 2)
  /\ bestOffset \in Indices
  /\ pc \in {"outerLoopCheck", "failureLookup", "innerLoop", "rematch",
              "followFailure", "postComparison", "increment"}

Init ==
  /\ \E s \in [Indices -> CharacterSet] :
       inputString = s
  /\ strLen = Len(inputString)
  /\ failure = [i \in Indices |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerLoopCheck"

OuterLoopCheck ==
  /\ pc = "outerLoopCheck"
  /\ \/ loopCounter < strLen * 2
       \/ (pc' = "failureLookup")
     /\ pc' = "failureLookup"
     /\ UNCHANGED << inputString, strLen, failure, matchIdx, loopCounter, bestOffset >>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ pc' = "innerLoop"
  /\ matchIdx' = failure[(loopCounter - 1) % strLen]
  /\ UNCHANGED << inputString, strLen, failure, loopCounter, bestOffset >>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET curChar == inputString[loopCounter % strLen]
         candChar == inputString[(bestOffset + loopCounter) % strLen] IN
       /\ IF curChar # candChar /\ matchIdx # Sentinel
            THEN pc' = "rematch"
          ELSE pc' = "postComparison"
       /\ matchIdx' = IF curChar # candChar /\ matchIdx # Sentinel
                        THEN failure[matchIdx]
                        ELSE matchIdx
  /\ UNCHANGED << inputString, strLen, failure, loopCounter, bestOffset >>

Rematch ==
  /\ pc = "rematch"
  /\ LET curChar == inputString[loopCounter % strLen]
         candChar == inputString[(bestOffset + loopCounter) % strLen] IN
       /\ bestOffset' = IF curChar < candChar THEN loopCounter % strLen ELSE bestOffset
       /\ matchIdx' = failure[matchIdx]
  /\ pc' = "innerLoop"
  /\ UNCHANGED << inputString, strLen, failure, loopCounter >>

PostComparison ==
  /\ pc = "postComparison"
  /\ LET curChar == inputString[loopCounter % strLen]
         candChar == inputString[(bestOffset + loopCounter) % strLen] IN
       /\ bestOffset' = IF curChar < candChar /\ matchIdx = Sentinel
                          THEN loopCounter % strLen
                        ELSE bestOffset
       /\ failure' = IF matchIdx = Sentinel
                       THEN [failure EXCEPT ![(loopCounter - 1) % strLen] = Sentinel]
                       ELSE [failure EXCEPT ![(loopCounter - 1) % strLen] = matchIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED << inputString, strLen, matchIdx, loopCounter >>

Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerLoopCheck"
  /\ UNCHANGED << inputString, strLen, failure, matchIdx, bestOffset >>

Terminate ==
  /\ pc = "outerLoopCheck"
  /\ loopCounter >= strLen * 2
  /\ UNCHANGED vars

Next ==
  \/ OuterLoopCheck \/ FailureLookup \/ InnerLoop \/ Rematch
  \/ PostComparison \/ Increment \/ Terminate

Spec == Init /\ [][Next]_vars

Correctness ==
  /\ \A i \in 0..(strLen - 1) :
       \A j \in 0..(strLen - 1) :
         LET rotA == [k \in 0..(strLen - 1) |->
                         inputString[(bestOffset + k) % strLen]]
             rotB == [k \in 0..(strLen - 1) |->
                         inputString[(j + k) % strLen]] IN
           \/ (rotA = rotB /\ bestOffset <= j)
            \/ (rotA # rotB => rotA < rotB)
  /\ bestOffset \in 0..(strLen - 1)

Termination == WF_vars(OuterLoopCheck) /\ WF_vars(Increment)

====