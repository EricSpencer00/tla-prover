---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* This module implements Booth's lexicographically-least circular substring
\* algorithm (J. Booth, 1980) over a nondeterministically-chosen input string.
\* The entire string set -- every zero-indexed sequence over a finite character
\* set up to a bounded length -- is explored. The algorithm builds a failure
\* function like KMP's and walks a doubled string (0 to 2*len-1) to handle the
\* circular wrap-around without an explicit "circular indexing" operator. The
\* safety properties are a type-correctness check and a functional correctness
\* statement that the chosen offset really does produce the minimal rotation.

CONSTANTS CharacterSet

NoMatch == Cardinality(CharacterSet)
MaxLength == 3

VARIABLES inputString, stringLength, failure, matchIndex, loopCounter, bestOffset, pc
vars == <<inputString, stringLength, failure, matchIndex, loopCounter, bestOffset, pc>>

InitString == CHOOSE s \in (0..(NoMatch - 1))(2^MaxLength) : Len(s) = MaxLength

TypeInvariant ==
  /\ inputString \in (0..(NoMatch - 1))(2^MaxLength)
  /\ stringLength = Len(inputString)
  /\ failure \in [0..(2*MaxLength) -> 0..(2*MaxLength) \cup {NoMatch}]
  /\ matchIndex \in 0..(2*MaxLength) \cup {NoMatch}
  /\ loopCounter \in 1..(2*MaxLength)
  /\ bestOffset \in 0..(MaxLength - 1)
  /\ pc \in {"enclosed", "failureLookup", "innerLoop", "candidateBetter", "followChain", "postCompare", "resume"}

Enclosed == [string |-> inputString, failure |-> failure, offset |-> bestOffset]
LoopBack == [string |-> Enclosed.string, failure |-> Enclosed.failure, offset |-> (Enclosed.offset + 1) % MaxLength]

Init ==
  /\ inputString = InitString
  /\ stringLength = MaxLength
  /\ failure = [i \in 0..(2*MaxLength) |-> NoMatch]
  /\ matchIndex = NoMatch
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "enclosed"

OuterCheck ==
  /\ pc = "enclosed"
  /\ loopCounter < 2 * MaxLength
  /\ pc' = "failureLookup"
  /\ UNCHANGED <<inputString, stringLength, failure, matchIndex, loopCounter, bestOffset>>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ matchIndex' = failure[loopCounter - bestOffset]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, stringLength, failure, loopCounter, bestOffset>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET curChar == inputString[(loopCounter) % stringLength]
         candChar == inputString[(bestOffset + matchIndex) % stringLength] IN
    IF curChar # candChar /\ matchIndex # NoMatch
      THEN pc' = "candidateBetter"
      ELSE pc' = "postCompare"
  /\ UNCHANGED <<inputString, stringLength, failure, bestOffset, loopCounter>>

CandidateBetter ==
  /\ pc = "candidateBetter"
  /\ LET curChar == inputString[(loopCounter) % stringLength]
         candChar == inputString[(bestOffset + matchIndex) % stringLength] IN
    /\ curChar < candChar
    /\ bestOffset' = (loopCounter + matchIndex) % stringLength
  /\ pc' = "followChain"
  /\ UNCHANGED <<inputString, stringLength, failure, matchIndex, loopCounter>>

FollowChain ==
  /\ pc = "followChain"
  /\ matchIndex' = failure[matchIndex]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, stringLength, failure, bestOffset, loopCounter>>

PostCompare ==
  /\ pc = "postCompare"
  /\ LET curChar == inputString[(loopCounter) % stringLength]
         candChar == inputString[(bestOffset + matchIndex) % stringLength] IN
    /\ curChar # candChar
    /\ matchIndex = NoMatch
    /\ bestOffset' = IF curChar < candChar THEN loopCounter % stringLength ELSE bestOffset
    /\ failure' = [failure EXCEPT ![loopCounter] = IF curChar = candChar THEN NoMatch ELSE matchIndex + 1]
  /\ pc' = "resume"
  /\ UNCHANGED <<inputString, stringLength, matchIndex, loopCounter>>

Resume ==
  /\ pc = "resume"
  /\ loopCounter < 2 * MaxLength
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "enclosed"
  /\ UNCHANGED <<inputString, stringLength, failure, matchIndex, bestOffset>>

Stall ==
  /\ pc = "enclosed"
  /\ loopCounter = 2 * MaxLength
  /\ UNCHANGED vars

Next == OuterCheck \/ FailureLookup \/ InnerLoop \/ CandidateBetter \/ FollowChain \/ PostCompare \/ Resume \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup) /\ WF_vars(Resume)

Correctness ==
  /\ \A i \in 0..(stringLength - 1) : LoopBack.string[i] <= LoopBack.string[(bestOffset + i) % stringLength]
  /\ \A i \in 0..(stringLength - 1) : LoopBack.string[i] = LoopBack.string[(bestOffset + i) % stringLength] => bestOffset <= i

Termination == <>(pc = "enclosed" /\ loopCounter = 2 * MaxLength)

====