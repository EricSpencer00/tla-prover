---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  CharacterSet

VARIABLES
  inputString, strLen, failFunc, matchIdx, loopCounter, bestOffset, pc

vars == <<inputString, strLen, failFunc, matchIdx, loopCounter, bestOffset, pc>>

\* A modified character set: the .cfg replaces Nat with a finite version, but
\* we keep EXTENDS Naturals so everything below still works.
ZSequences == CharacterSet

Sentinel == -1

Corpus == [n \in Nat |-> <<>>] \cup
          [n \in Nat |-> <<[1..n -> CHOOSE c \in ZSequences : TRUE]>>]

TypeInvariant ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ failFunc \in [0..(2 * strLen) -> (Nat \cup {Sentinel})]
  /\ matchIdx \in (Nat \cup {Sentinel})
  /\ loopCounter \in Nat
  /\ bestOffset \in 0..(strLen - 1)
  /\ pc \in {"outer_check", "lookup", "inner_compare", "reset_failure", "post_compare", "increment"}

Init ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ failFunc = [i \in 0..(2 * strLen) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outer_check"

OuterCheck ==
  /\ pc = "outer_check"
  /\ IF loopCounter < (2 * strLen) THEN pc' = "lookup" ELSE pc' = "outer_check"
  /\ UNCHANGED <<inputString, strLen, failFunc, matchIdx, loopCounter, bestOffset>>

LookupFailure ==
  /\ pc = "lookup"
  /\ failFunc' = [failFunc EXCEPT ![(loopCounter - 1) + bestOffset] = @]
  /\ pc' = "inner_compare"
  /\ UNCHANGED <<inputString, strLen, matchIdx, loopCounter, bestOffset>>

\* Compare the current character with its candidate; mod handles circular indexing.
InnerCompare ==
  /\ pc = "inner_compare"
  /\ LET curChar == inputString[(loopCounter % strLen) + 1]
         candChar == inputString[((bestOffset + matchIdx) % strLen) + 1]
     IN
       /\ curChar # candChar
       /\ IF matchIdx = Sentinel
          THEN pc' = "post_compare"
          ELSE pc' = "inner_compare"
       /\ IF curChar < candChar
          THEN bestOffset' = loopCounter % strLen
          ELSE bestOffset' = bestOffset
  /\ UNCHANGED <<inputString, strLen, failFunc, matchIdx, loopCounter>>

\* Follow the failure chain; this is the linear-time trick.
ResetFailure ==
  /\ pc = "inner_compare"
  /\ matchIdx # Sentinel
  /\ matchIdx' = failFunc[matchIdx]
  /\ pc' = "inner_compare"
  /\ UNCHANGED <<inputString, strLen, failFunc, loopCounter, bestOffset>>

PostCompare ==
  /\ pc = "post_compare"
  /\ LET curChar == inputString[(loopCounter % strLen) + 1]
         candChar == inputString[((bestOffset + matchIdx) % strLen) + 1]
     IN
       /\ curChar # candChar
       /\ IF curChar < candChar THEN bestOffset' = loopCounter % strLen ELSE bestOffset' = bestOffset
  /\ failFunc' = [failFunc EXCEPT ![(loopCounter - 1) + bestOffset] = IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, matchIdx, loopCounter>>

Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outer_check"
  /\ UNCHANGED <<inputString, strLen, failFunc, matchIdx, bestOffset>>

Stall ==
  /\ pc = "outer_check"
  /\ loopCounter >= (2 * strLen)
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ LookupFailure
  \/ InnerCompare
  \/ ResetFailure
  \/ PostCompare
  \/ Increment
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(LookupFailure)
        /\ WF_vars(InnerCompare) /\ WF_vars(ResetFailure) /\ WF_vars(PostCompare) /\ WF_vars(Increment)

RotAt(i) == <<[1..strLen |-> inputString[((i + # - 1) % strLen) + 1]]>>

\* Tie-breaking: if two rotations are equal, the one with the smaller shift
\* must be the best offset -- this pins the answer uniquely.
Correctness ==
  /\ \A i \in 0..(strLen - 1): RotAt(bestOffset) <= RotAt(i)
  /\ \A i \in 0..(strLen - 1):
       RotAt(i) = RotAt(bestOffset) => (i >= bestOffset)
  /\ bestOffset \in 0..(strLen - 1)

Termination == <>(pc = "outer_check" /\ loopCounter >= (2 * strLen))

====