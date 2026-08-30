---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS CharacterSet

\* Zero-indexed strings over a finite character set, with length up to a bound.
\* The corpus is the set of all such strings; the model checker explores it.
Corpus == UNION {[1..n -> CharacterSet] : n \in 1..MaxStringLength}

NoIndex == -1

VARIABLES
  inputString,    \* the nondeterministically chosen zero-indexed character sequence
  stringLength,   \* length of inputString
  failure,        \* failure function array [0..2*MaxStringLength -> index or NoIndex]
  patternIndex,   \* current failure function lookup during the inner loop
  loopCounter,    \* outer loop counter, 1 .. 2*MaxStringLength
  bestOffset,     \* start position of the lexicographically smallest rotation found
  pc              \* program counter: which labeled step of the algorithm is active

vars == <<inputString, stringLength, failure, patternIndex, loopCounter, bestOffset, pc>>

TypeInvariant ==
  /\ inputString \in Corpus
  /\ stringLength = Len(inputString)
  /\ failure \in [0..(2 * MaxStringLength) -> (0..MaxStringLength) \cup {NoIndex}]
  /\ patternIndex \in (0..MaxStringLength) \cup {NoIndex}
  /\ loopCounter \in 1..(2 * MaxStringLength)
  /\ bestOffset \in 0..(MaxStringLength - 1)
  /\ pc \in {"OuterLoopEntry", "FailureLookup", "InnerCompLoop", "UpdateOffset",
              "FollowFailure", "PostComp", "Terminated"}

Init ==
  /\ \E s \in Corpus : inputString = s
  /\ stringLength = Len(inputString)
  /\ failure = [i \in 0..(2 * MaxStringLength) |-> NoIndex]
  /\ patternIndex = NoIndex
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "OuterLoopEntry"

OuterLoopEntry ==
  /\ pc = "OuterLoopEntry"
  /\ IF loopCounter < (2 * stringLength)
       THEN pc' = "FailureLookup"
       ELSE pc' = "Terminated"
  /\ UNCHANGED <<inputString, stringLength, failure, patternIndex, loopCounter, bestOffset>>

FailureLookup ==
  /\ pc = "FailureLookup"
  /\ patternIndex' = failure[loopCounter - 1]
  /\ pc' = "InnerCompLoop"
  /\ UNCHANGED <<inputString, stringLength, failure, loopCounter, bestOffset>>

\* Compare the current character with the candidate candidate character, following the
\* failure chain if there is one and the characters differ.
InnerCompLoop ==
  /\ pc = "InnerCompLoop"
  /\ LET curChar == inputString[(loopCounter - 1) % stringLength]
         candChar == inputString[(bestOffset + loopCounter - 1) % stringLength]
     IN IF curChar # candChar /\ patternIndex # NoIndex
           THEN pc' = "UpdateOffset" \/ pc' = "FollowFailure"
           ELSE pc' = "PostComp"
  /\ UNCHANGED <<inputString, stringLength, failure, patternIndex, loopCounter, bestOffset>>

\* The candidate character is strictly greater, so a new smallest rotation is found.
UpdateOffset ==
  /\ pc \in {"UpdateOffset", "FollowFailure"}
  /\ LET curChar == inputString[(loopCounter - 1) % stringLength]
         candChar == inputString[(bestOffset + loopCounter - 1) % stringLength]
     IN IF curChar < candChar THEN bestOffset' = loopCounter - 1 ELSE bestOffset' = bestOffset
  /\ pc' = "FollowFailure"
  /\ UNCHANGED <<inputString, stringLength, failure, patternIndex, loopCounter>>

FollowFailure ==
  /\ pc = "FollowFailure"
  /\ patternIndex' = IF patternIndex = NoIndex THEN NoIndex ELSE failure[patternIndex]
  /\ pc' = "InnerCompLoop"
  /\ UNCHANGED <<inputString, stringLength, failure, loopCounter, bestOffset>>

\* After the inner loop exits, set the failure entry appropriately and move on.
PostComp ==
  /\ pc = "PostComp"
  /\ LET curChar == inputString[(loopCounter - 1) % stringLength]
         candChar == inputString[(bestOffset + loopCounter - 1) % stringLength]
     IN IF curChar < candChar THEN bestOffset' = loopCounter - 1 ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![loopCounter] =
                   IF patternIndex = NoIndex
                     THEN NoIndex
                     ELSE patternIndex + 1]
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "OuterLoopEntry"
  /\ UNCHANGED <<inputString, stringLength, patternIndex>>

Terminated ==
  /\ pc = "Terminated"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoopEntry
  \/ FailureLookup
  \/ InnerCompLoop
  \/ UpdateOffset
  \/ FollowFailure
  \/ PostComp
  \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoopEntry) /\ WF_vars(FailureLookup)
                          /\ WF_vars(InnerCompLoop) /\ WF_vars(UpdateOffset)
                          /\ WF_vars(FollowFailure) /\ WF_vars(PostComp)

\* Lexicographic minimality: the rotation at bestOffset is not greater than any other.
Correctness ==
  \A i \in 1..stringLength :
    LET rotA(j) == inputString[(i + j - 1) % stringLength]
        rotB(j) == inputString[(bestOffset + j - 1) % stringLength]
    IN (rotA \in Seq(CharacterSet) /\ rotB \in Seq(CharacterSet))
         /\ \A j \in 1..stringLength : rotA(j) <= rotB(j)
         /\ (rotA = rotB => i >= bestOffset)

Termination == <>(pc = "Terminated")

====