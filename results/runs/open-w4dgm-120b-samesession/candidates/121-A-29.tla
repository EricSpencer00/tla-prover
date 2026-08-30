---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

VARIABLES inputString, strLen, failFn, backtrack, loopCounter, bestOffset, pc

vars == <<inputString, strLen, failFn, backtrack, loopCounter, bestOffset, pc>>

Sentinel == 0
MaxLoop == 2 * 3

TypeInvariant ==
  /\ inputString \in [1..3 -> CharacterSet]
  /\ strLen = Len(inputString)
  /\ failFn \in [0..MaxLoop -> 0..MaxLoop]
  /\ backtrack \in (0..MaxLoop) \cup {Sentinel}
  /\ loopCounter \in 1..MaxLoop
  /\ bestOffset \in 0..(strLen - 1)
  /\ pc \in {"outer", "lookup", "inner", "post", "done"}

Init ==
  /\ \E s \in [1..3 -> CharacterSet] : inputString = s
  /\ strLen = Len(inputString)
  /\ failFn = [i \in 0..MaxLoop |-> Sentinel]
  /\ backtrack = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterCheck ==
  /\ pc = "outer"
  /\ pc' = IF loopCounter < MaxLoop THEN "lookup" ELSE "done"
  /\ UNCHANGED <<inputString, strLen, failFn, backtrack, loopCounter, bestOffset>>

FailureLookup ==
  /\ pc = "lookup"
  /\ backtrack' = failFn[loopCounter - bestOffset]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, strLen, failFn, loopCounter, bestOffset>>

InnerLoop ==
  /\ pc = "inner"
  /\ IF inputString[(loopCounter % strLen) + 1] # inputString[(bestOffset + loopCounter) % strLen + 1]
        THEN IF backtrack # Sentinel THEN pc' = "post"
             ELSE pc' = "post"
       ELSE pc' = "post"
  /\ UNCHANGED <<inputString, strLen, failFn, backtrack, loopCounter, bestOffset>>

UpdateOnLess ==
  /\ pc = "post"
  /\ IF inputString[(loopCounter % strLen) + 1] < inputString[(bestOffset + loopCounter) % strLen + 1]
        THEN bestOffset' = loopCounter
        ELSE bestOffset' = bestOffset
  /\ backtrack' = IF backtrack = Sentinel THEN Sentinel ELSE backtrack + 1
  /\ failFn' = [failFn EXCEPT ![loopCounter] = IF backtrack = Sentinel THEN Sentinel ELSE backtrack + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, loopCounter>>

IncrementCounter ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, strLen, failFn, backtrack, bestOffset>>

Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ FailureLookup
  \/ InnerLoop
  \/ UpdateOnLess
  \/ IncrementCounter
  \/ Stutter

Spec == Init /\ [][Next]_vars
    /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup) /\ WF_vars(InnerLoop)
    /\ WF_vars(UpdateOnLess) /\ WF_vars(IncrementCounter)

RotationAt(n) == <<inputString[(n % strLen) + 1], inputString[((n + 1) % strLen) + 1], inputString[((n + 2) % strLen) + 1]>>

Correctness ==
  /\ \A i \in 0..(strLen - 1) : RotationAt(bestOffset) <= RotationAt(i)
  /\ \A i \in 0..(strLen - 1) : RotationAt(bestOffset) = RotationAt(i) => bestOffset <= i

Termination == <>(pc = "done")

====