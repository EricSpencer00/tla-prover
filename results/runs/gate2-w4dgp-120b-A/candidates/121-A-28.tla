---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, ZSequences

CONSTANTS CharacterSet

VARIABLES stringInput, stringLen, failFunc, pIdx, loopIdx, bestOffset, pc

vars == <<stringInput, stringLen, failFunc, pIdx, loopIdx, bestOffset, pc>>

Sentinel == -1
MaxLen == 3

RECURSIVE Seq(_)
Seq(S) == IF S = {} THEN <<>> ELSE LET x == CHOOSE y \in S : TRUE IN <<x>> \o Seq(S \ {x})

\* The corpus is the set of all zero-indexed sequences of length 1..MaxLen over the
\* character set (the constant below enforces a small, finite alphabet for TLC).
StringCorpus == {s \in 0..(MaxLen - 1) -> CharacterSet : s \in (1..MaxLen)}

InitString == CHOOSE s \in StringCorpus : TRUE

CharAt(idx) == stringInput[idx]

TypeInvariant ==
  /\ stringInput \in StringCorpus
  /\ stringLen = Len(stringInput)
  /\ failFunc \in [0..(2 * stringLen) -> Sentinel..(stringLen - 1)]
  /\ pIdx \in Sentinel..(stringLen - 1)
  /\ loopIdx \in 1..(2 * stringLen)
  /\ bestOffset \in 0..(stringLen - 1)
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "UpdateOnLess", "FollowChain", "PostCompare", "Terminate"}

Init ==
  /\ stringInput = InitString
  /\ stringLen = Len(InitString)
  /\ failFunc = [i \in 0..(2 * Len(InitString)) |-> Sentinel]
  /\ pIdx = Sentinel
  /\ loopIdx = 1
  /\ bestOffset = 0
  /\ pc = "OuterCheck"

OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF loopIdx < (2 * stringLen)
       THEN pc' = "Lookup"
       ELSE pc' = "Terminate"
  /\ UNCHANGED <<stringInput, stringLen, failFunc, pIdx, loopIdx, bestOffset>>

LookupFailureFunction ==
  /\ pc = "Lookup"
  /\ pIdx' = failFunc[loopIdx - 1]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<stringInput, stringLen, failFunc, loopIdx, bestOffset>>

\* The inner loop keeps advancing the failure-chain until the characters differ or
\* the chain is exhausted (pIdx=SENTINEL).
InnerLoop ==
  /\ pc = "InnerLoop"
  /\ IF CharAt(loopIdx % stringLen) = CharAt((bestOffset + pIdx) % stringLen)
       THEN IF pIdx # Sentinel
              THEN /\ pIdx' = failFunc[pIdx]
                   /\ UNCHANGED <<stringInput, stringLen, failFunc, loopIdx, bestOffset, pc>>
              ELSE /\ pc' = "PostCompare"
                   /\ UNCHANGED <<stringInput, stringLen, failFunc, pIdx, loopIdx, bestOffset>>
       ELSE /\ pc' = "UpdateOnLess"
            /\ UNCHANGED <<stringInput, stringLen, failFunc, pIdx, loopIdx, bestOffset>>

UpdateOnLess ==
  /\ pc = "UpdateOnLess"
  /\ CharAt(loopIdx % stringLen) < CharAt((bestOffset + pIdx) % stringLen)
  /\ bestOffset' = loopIdx % stringLen
  /\ pc' = "FollowChain"
  /\ UNCHANGED <<stringInput, stringLen, failFunc, pIdx, loopIdx>>

FollowChain ==
  /\ pc = "FollowChain"
  /\ pIdx' = failFunc[pIdx]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<stringInput, stringLen, failFunc, loopIdx, bestOffset>>

\* Bottom-of-loop housekeeping: reset or extend the failure function entry.
PostCompare ==
  /\ pc = "PostCompare"
  /\ IF CharAt(loopIdx % stringLen) < CharAt(bestOffset % stringLen)
       THEN bestOffset' = loopIdx % stringLen
       ELSE bestOffset' = bestOffset
  /\ failFunc' = [failFunc EXCEPT ![loopIdx] = IF pIdx = Sentinel THEN Sentinel ELSE (pIdx + 1)]
  /\ pc' = "OuterCheck"
  /\ loopIdx' = loopIdx + 1
  /\ UNCHANGED <<stringInput, stringLen, pIdx>>

Terminate ==
  /\ pc = "Terminate"
  /\ UNCHANGED vars

Next == OuterCheck \/ LookupFailureFunction \/ InnerLoop \/ UpdateOnLess \/ FollowChain \/ PostCompare \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(LookupFailureFunction) /\ WF_vars(InnerLoop) /\ WF_vars(PostCompare)

\* Correctness: at termination the identified offset yields the lexicographically-
\* smallest rotation, and when several rotations are equal it yields the smallest shift.
Correctness ==
  /\ pc = "Terminate"
  /\ \A i \in 0..(stringLen - 1) :
       LET rot(i) == <<CharAt((i + j) % stringLen) : j \in 0..(stringLen - 1)>>
       IN  (rot(bestOffset) # rot(i) => rot(bestOffset) < rot(i))
           /\ (rot(bestOffset) = rot(i) => bestOffset <= i)

Termination == <>(pc = "Terminate")

====