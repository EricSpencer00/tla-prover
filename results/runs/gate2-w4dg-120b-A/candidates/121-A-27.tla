---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* Lexicographically-least circular substring (Booth's algorithm) over a
\* nondeterministically chosen input string.  Arrays are zero-indexed, and
\* the failure function is built and followed like in KMP.
\* The module declares exactly the identifiers the reference .cfg expects.

CONSTANTS CharacterSet, Nat
Sentinel == Nat

VARIABLES inputString, strLen, failFn, pIdx, loopIdx, bestOff, pc
vars == <<inputString, strLen, failFn, pIdx, loopIdx, bestOff, pc>>

\* Zero-indexed sequences: s[0] is the first character, s[k] the (k+1)-th.
Corpus == UNION {[1..n -> CharacterSet] : n \in Nat}

InitFn == [k \in 0..(2 * strLen - 1) |-> Sentinel]

TypeInvariant ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ failFn \in [0..(2 * strLen - 1) -> 0..Nat \cup {Sentinel}]
  /\ pIdx \in 0..Nat \cup {Sentinel}
  /\ loopIdx \in 1..(2 * strLen)
  /\ bestOff \in 0..(strLen - 1)
  /\ pc \in {"outerCheck", "failLookup", "compare", "updateBest",
             "followChain", "postCompare", "increment", "final"}

Init ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ failFn = InitFn
  /\ pIdx = Sentinel
  /\ loopIdx = 1
  /\ bestOff = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopIdx < (2 * strLen) THEN pc' = "failLookup" ELSE pc' = "final"
  /\ UNCHANGED <<inputString, strLen, failFn, pIdx, loopIdx, bestOff>>

FailLookup ==
  /\ pc = "failLookup"
  /\ pIdx' = failFn[loopIdx - 1]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, strLen, failFn, loopIdx, bestOff>>

CurrentChar == inputString[(loopIdx - 1) % strLen]
CandidateChar == inputString[(bestOff + pIdx) % strLen]

Compare ==
  /\ pc = "compare"
  /\ IF CurrentChar # CandidateChar /\ pIdx # Sentinel
       THEN pc' = "updateBest"
       ELSE pc' = "postCompare"
  /\ UNCHANGED <<inputString, strLen, failFn, pIdx, loopIdx, bestOff>>

UpdateBest ==
  /\ pc = "updateBest"
  /\ bestOff' = IF CurrentChar < CandidateChar THEN loopIdx - 1 ELSE bestOff
  /\ pIdx' = failFn[pIdx]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, strLen, failFn, loopIdx>>

PostCompare ==
  /\ pc = "postCompare"
  /\ IF CurrentChar # CandidateChar /\ pIdx = Sentinel
       THEN bestOff' = IF CurrentChar < CandidateChar THEN loopIdx - 1 ELSE bestOff
       ELSE bestOff' = bestOff
  /\ failFn' = [failFn EXCEPT ![loopIdx - 1] =
                   IF CurrentChar # CandidateChar
                     THEN IF pIdx = Sentinel THEN Sentinel ELSE pIdx + 1
                     ELSE Sentinel]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, pIdx, loopIdx>>

Increment ==
  /\ pc = "increment"
  /\ loopIdx' = loopIdx + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, strLen, failFn, pIdx, bestOff>>

Stutter ==
  /\ pc = "final"
  /\ UNCHANGED vars

Next == OuterCheck \/ FailLookup \/ Compare \/ UpdateBest \/ PostCompare
        \/ Increment \/ Stutter

Spec == Init /\ [][Next]_vars
        /\ WF_vars(OuterCheck) /\ WF_vars(FailLookup) /\ WF_vars(Compare)

\* The best offset must name the lexicographically-minimal rotation of the
\* input string, and for equal rotations it must be the smallest shift.
Correctness ==
  /\ bestOff >= 0
  /\ \A k \in 0..(strLen - 1) :
       LET rot(b) == inputString[(b + k) % strLen] IN
         (rot(bestOff) < rot(k)) \/ (rot(bestOff) = rot(k) /\ bestOff <= k)

Termination == <>(pc = "final")

====