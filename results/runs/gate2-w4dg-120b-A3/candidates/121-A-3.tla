---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  CharacterSet

Sentinel == -1

VARIABLES
  inputString, length, failure, patIdx, loopVar, bestOffset, pc

vars == <<inputString, length, failure, patIdx, loopVar, bestOffset, pc>>

Corpus == Union({[1 .. n -> CharacterSet] : n \in Nat})

MaxLen == 2
ValidIndices == 0 .. (2 * MaxLen) - 1

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure \in [ValidIndices -> {-1} \cup ValidIndices]
  /\ patIdx \in {-1} \cup ValidIndices
  /\ loopVar \in 1 .. (2 * MaxLen)
  /\ bestOffset \in 0 .. (length - 1)
  /\ pc \in {"outer", "lookup", "inner", "post", "final"}

Init ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure = [i \in ValidIndices |-> -1]
  /\ patIdx = -1
  /\ loopVar = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterStep ==
  /\ pc = "outer"
  /\ \/ \A i \in ValidIndices : failure' = [failure EXCEPT ![i] = -1]
     \/ TRUE
  /\ IF loopVar < 2 * length
       THEN pc' = "lookup"
       ELSE pc' = "final"
  /\ UNCHANGED <<inputString, length, patIdx, loopVar, bestOffset>>

LookupStep ==
  /\ pc = "lookup"
  /\ patIdx' = failure[(loopVar - 1) % length + bestOffset]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, length, failure, loopVar, bestOffset>>

InnerStep ==
  /\ pc = "inner"
  /\ LET curChar == inputString[(loopVar - 1) % length + 1]
         candChar == inputString[(loopVar + patIdx) % length + 1]
     IN \/ /\ curChar # candChar
           /\ patIdx # -1
           /\ pc' = "inner"
           /\ UNCHANGED <<failure, patIdx, loopVar, bestOffset>>
        \/ \/ /\ curChar = candChar
              \/ /\ curChar # candChar
                 /\ patIdx = -1
           /\ pc' = "post"
           /\ UNCHANGED <<failure, patIdx, loopVar, bestOffset>>
        \/ /\ curChar # candChar
           /\ patIdx # -1
           /\ curChar < candChar
           /\ bestOffset' = (loopVar + patIdx) % length
           /\ pc' = "inner"
           /\ UNCHANGED <<inputString, length, failure, patIdx, loopVar>>
        \/ /\ curChar # candChar
           /\ patIdx # -1
           /\ curChar > candChar
           /\ patIdx' = failure[patIdx]
           /\ pc' = "inner"
           /\ UNCHANGED <<inputString, length, failure, loopVar, bestOffset>>

PostStep ==
  /\ pc = "post"
  /\ LET curChar == inputString[(loopVar - 1) % length + 1]
         candChar == inputString[(loopVar + patIdx) % length + 1]
     IN /\ bestOffset' = IF (curChar # candChar /\ patIdx = -1 /\ curChar < candChar)
                           THEN (loopVar + patIdx) % length
                           ELSE bestOffset
        /\ failure' = [failure EXCEPT ![(loopVar - 1) % length + bestOffset] =
                          IF curChar # candChar /\ patIdx = -1
                            THEN -1
                            ELSE patIdx + 1]
        /\ pc' = "outer"
        /\ UNCHANGED <<inputString, length, patIdx, loopVar>>

LoopVarStep ==
  /\ pc = "outer"
  /\ loopVar < 2 * length
  /\ loopVar' = loopVar + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, length, failure, patIdx, bestOffset>>

Stall ==
  /\ pc = "final"
  /\ UNCHANGED vars

Next ==
  \/ OuterStep \/ LookupStep \/ InnerStep \/ PostStep \/ LoopVarStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopVarStep)

Correctness ==
  /\ \A shift \in 0 .. (length - 1) :
       LET rot(k) == inputString[(k + shift) % length + 1]
           bestRot(k) == inputString[(k + bestOffset) % length + 1]
       IN \A k \in 1 .. length : bestRot(k) <= rot(k)
  /\ \A shift \in 0 .. (length - 1) :
       (bestRot = (LAMBDA k \in 1 .. length : inputString[(k + shift) % length + 1]))
         => shift >= bestOffset

Termination == <>(pc = "final")

====