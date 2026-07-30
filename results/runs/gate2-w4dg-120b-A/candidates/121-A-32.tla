---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, Nat

\* An entry of the failure function that has not been set yet.
\* Must be a Nat that is outside the range 0..2*MaxStringLength-1.
\* The concrete value is provided by the model-checking configuration.
FailureUndefined == Nat

VARIABLES inputString, n, failure, matchIdx, loop, bestOff, pc

vars == <<inputString, n, failure, matchIdx, loop, bestOff, pc>>

\* Zero-indexed rotation: the smallest rotation starts at bestOff, and
\* the character at position i (mod n) of that rotation is inputString[(i + bestOff) % n].
TypeInvariant ==
  /\ inputString \in STRING(CharacterSet)
  /\ n = Len(inputString)
  /\ failure \in [0..(2*n - 1) -> {FailureUndefined} \cup (0..(2*n - 1))]
  /\ matchIdx \in {FailureUndefined} \cup (0..(2*n - 1))
  /\ loop \in 1..(2*n)
  /\ bestOff \in 0..(n - 1)
  /\ pc \in {"outerCheck", "lookup", "inner", "reset", "postCompare", "increment", "halt"}

Init ==
  /\ inputString \in STRING(CharacterSet)
  /\ n = Len(inputString)
  /\ failure = [i \in 0..(2*n - 1) |-> FailureUndefined]
  /\ matchIdx = FailureUndefined
  /\ loop = 1
  /\ bestOff = 0
  /\ pc = "outerCheck"

\* Outer loop runs from 1 up to (but not including) twice the string length.
OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loop < 2*n THEN pc' = "lookup" ELSE pc' = "halt"
  /\ UNCHANGED <<inputString, n, failure, matchIdx, loop, bestOff>>

Lookup ==
  /\ pc = "lookup"
  /\ matchIdx' = failure[(loop + bestOff) % n]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, n, failure, loop, bestOff>>

\* compare the character at the current position with the character
\* at the candidate position derived from the failure function.
Inner ==
  /\ pc = "inner"
  /\ IF inputString[loop % n] # inputString[(matchIdx + bestOff) % n]
        /\ matchIdx # FailureUndefined
     THEN pc' = "reset"
     ELSE pc' = "postCompare"
  /\ UNCHANGED <<inputString, n, failure, matchIdx, loop, bestOff>>

Reset ==
  /\ pc = "reset"
  /\ matchIdx' = failure[matchIdx]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, n, failure, loop, bestOff>>

\* A strictly smaller character updates the best rotation offset.
UpdateBest ==
  /\ inputString[loop % n] < inputString[(matchIdx + bestOff) % n]
  /\ bestOff' = loop % n
  /\ UNCHANGED <<inputString, n, failure, matchIdx, loop>>

PostCompare ==
  /\ pc = "postCompare"
  /\ LET fnext == IF matchIdx = FailureUndefined THEN FailureUndefined ELSE matchIdx + 1 IN
       /\ failure' = [failure EXCEPT ![(loop + bestOff) % n] = fnext]
       /\ bestOff' = IF inputString[loop % n] # inputString[(matchIdx + bestOff) % n]
                       /\ inputString[loop % n] < inputString[(matchIdx + bestOff) % n]
                       THEN loop % n
                       ELSE bestOff
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, n, matchIdx, loop>>

Increment ==
  /\ pc = "increment"
  /\ loop' = loop + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, n, failure, matchIdx, bestOff>>

Halt ==
  /\ pc = "halt"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ Inner \/ Reset \/ PostCompare \/ Increment \/ Halt

\* The lexicographically-minimal rotation is the smallest of all cyclic
\* rotations, and among equal rotations it has the smallest shift.
Correctness ==
  /\ \A i \in 0..(n - 1) :
       inputString[(bestOff + i) % n] <= inputString[i]
  /\ \A i \in 0..(n - 1) :
       (inputString[(bestOff + i) % n] = inputString[i] /\ bestOff < i)
         => \A j \in 0..(n - 1) : inputString[(i + j) % n] >= inputString[j]

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "halt")

====