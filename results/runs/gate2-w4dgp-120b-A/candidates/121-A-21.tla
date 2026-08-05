---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(*=============================================================================*)
(*  The lexicographically-least circular substring algorithm from the 1980       *)
(*  Booth paper (doi:10.1016/0020-0190(80)90149-0).  The input is a zero-indexed  *)
(*  circular string over a small character set; the algorithm computes the       *)
(*  rotation offset that yields the lexicographically smallest rotation, using  *)
(*  a failure function array (like KMP) to achieve linear time.                  *)
(*=============================================================================*)

CONSTANTS
  CharacterSet

ASSUME CharacterSet \subseteq Nat

VARIABLES
  inputString,         (\* zero-indexed sequence of characters, chosen nondeterministically from CharacterSet)
  length,              (\* length of inputString)
  failure,             (\* failure function array, indexed from 0 to twice the string length)
  patternIndex,        (\* pattern-match index tracking the current failure function lookup)
  loopCounter,         (\* outer loop counter, ranging from 1 to just below twice the string length)
  bestOffset,          (\* current best rotation offset, identifying the lexicographically smallest rotation found)
  pc                   (\* program counter: which labeled step of the algorithm is executing)

vars == <<inputString, length, failure, patternIndex, loopCounter, bestOffset, pc>>

UntypedStrings == UNION [0..n -> CharacterSet] : n \in Nat

Sentinel == 0
Undefined == 0

NextIndex(i) == (i + 1) % length

Init ==
  /\ inputString \in UntypedStrings
  /\ length = Len(inputString)
  /\ length >= 1
  /\ failure = [0 .. (2 * length) - 1 |-> Undefined]
  /\ patternIndex = Undefined
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "check_outer"

\* Outer loop check: continue while the loop counter is below twice the length.
CheckOuter ==
  /\ pc = "check_outer"
  /\ IF loopCounter < 2 * length
       THEN /\ pc' = "lookup_failure"
            /\ UNCHANGED <<inputString, length, failure, patternIndex, loopCounter, bestOffset>>
       ELSE /\ pc' = "terminate"
            /\ UNCHANGED <<inputString, length, failure, patternIndex, loopCounter, bestOffset>>

LookupFailure ==
  /\ pc = "lookup_failure"
  /\ failureIndex = (loopCounter + bestOffset) % length
  /\ patternIndex' = failure[failureIndex]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

\* Inner comparison loop: compare the character at the current loop position
\* (modulo length) with that at the candidate position (modulo length).  If
\* they differ and we are mid-match, continue looping; otherwise exit.
Compare ==
  /\ pc = "compare"
  /\ inputString[loopCounter % length] # inputString[(bestOffset + patternIndex) % length]
  /\ patternIndex # Undefined
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, length, failure, patternIndex, loopCounter, bestOffset>>

UpdateBestOnLess ==
  /\ pc = "compare"
  /\ inputString[loopCounter % length] # inputString[(bestOffset + patternIndex) % length]
  /\ inputString[loopCounter % length] < inputString[(bestOffset + patternIndex) % length]
  /\ patternIndex # Undefined
  /\ bestOffset' = loopCounter
  /\ pc' = "follow_failure"
  /\ UNCHANGED <<inputString, length, failure, patternIndex, loopCounter>>

FollowFailure ==
  /\ pc = "follow_failure"
  /\ patternIndex' = failure[patternIndex]
  /\ pc' = "post_compare"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

PostCompare ==
  /\ pc = "post_compare"
  /\ inputString[loopCounter % length] # inputString[(bestOffset + patternIndex) % length]
  /\ patternIndex = Undefined
  /\ LET newBest == IF inputString[loopCounter % length] < inputString[(bestOffset + patternIndex) % length]
                     THEN loopCounter ELSE bestOffset
                     IN bestOffset' = newBest
  /\ failure' = [failure EXCEPT ![failureIndex] = IF patternIndex = Undefined
                                            THEN Sentinel ELSE patternIndex + 1]
  /\ pc' = "increment_counter"
  /\ UNCHANGED <<inputString, length, patternIndex, loopCounter>>

\* Characters matched or both equal: reset the failure function and advance.
IncrementCounter ==
  /\ pc = "post_compare"
  /\ inputString[loopCounter % length] = inputString[(bestOffset + patternIndex) % length]
  /\ failure' = [failure EXCEPT ![failureIndex] = IF patternIndex = Undefined THEN Sentinel ELSE patternIndex + 1]
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "check_outer"
  /\ UNCHANGED <<inputString, length, patternIndex, bestOffset>>

Terminate ==
  /\ pc = "terminate"
  /\ pc' = "terminate"
  /\ UNCHANGED <<inputString, length, failure, patternIndex, loopCounter, bestOffset>>

Next ==
  \/ CheckOuter \/ LookupFailure \/ Compare \/ UpdateBestOnLess \/ FollowFailure
  \/ PostCompare \/ IncrementCounter \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(CheckOuter) /\ WF_vars(LookupFailure)
                     /\ WF_vars(Compare) /\ WF_vars(UpdateBestOnLess)
                     /\ WF_vars(FollowFailure) /\ WF_vars(PostCompare)
                     /\ WF_vars(IncrementCounter) /\ WF_vars(Terminate)

TypeInvariant ==
  /\ inputString \in UntypedStrings
  /\ length = Len(inputString)
  /\ length >= 1
  /\ failure \in [0 .. (2 * length) - 1 -> 0 .. length]
  /\ patternIndex \in 0 .. length
  /\ loopCounter \in 1 .. 2 * length
  /\ bestOffset \in 0 .. length - 1
  /\ pc \in {"check_outer", "lookup_failure", "compare", "follow_failure",
             "post_compare", "increment_counter", "terminate"}

\* Correctness: the identified rotation offset yields the lexicographically
\* smallest rotation of the input -- it is less-than-or-equal to every other.
Correctness ==
  /\ \A offset \in 0 .. length - 1 :
       LET shifted(b) == inputString[(b + offset) % length] IN
       LET shiftedBest == inputString[(b + bestOffset) % length] IN
       \A b \in 0 .. length - 1 :
         (shiftedBest < shifted) \/ ((shiftedBest = shifted) => (offset >= bestOffset))

Termination == <>(pc = "terminate")

====