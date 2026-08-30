---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences, ZSequences

CONSTANTS CharacterSet

\* Zero-indexed sequences over the character set; the corpus is all such
\* sequences up to the configured maximum length.
Corpus == UNION { [1..n -> CharacterSet] : n \in 1..MaxStringLength }

\* The sentinel value for the failure function entries.
Undefined == 0

VARIABLES inputString, stringLength, failureFunction, patternIndex,
          loopCounter, bestOffset, step

vars == <<inputString, stringLength, failureFunction, patternIndex,
          loopCounter, bestOffset, step>>

TypeOK ==
  /\ inputString \in Corpus
  /\ stringLength \in 0..MaxStringLength
  /\ failureFunction \in [0..2*MaxStringLength -> 0..MaxStringLength]
  /\ patternIndex \in 0..MaxStringLength
  /\ loopCounter \in 1..(2*MaxStringLength)
  /\ bestOffset \in 0..(MaxStringLength - 1)
  /\ step \in {"outerCheck", "failureLookup", "innerCompare", "postCompare"}

Init ==
  /\ \E s \in Corpus : inputString = s
  /\ stringLength = Len(inputString)
  /\ failureFunction = [i \in 0..2*MaxStringLength |-> Undefined]
  /\ patternIndex = Undefined
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ step = "outerCheck"

\* The outer loop runs past the end of the string to cover the doubled
\* interval; it never runs past the end of the array holding the failure
\* function, which is why the bound is twice the maximum string length.
OuterCheck ==
  /\ step = "outerCheck"
  /\ IF loopCounter < 2 * stringLength
       THEN step' = "failureLookup"
       ELSE step' = "halted"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex,
                 loopCounter, bestOffset>>

FailureLookup ==
  /\ step = "failureLookup"
  /\ patternIndex' = failureFunction[loopCounter - bestOffset]
  /\ step' = "innerCompare"
  /\ UNCHANGED <<inputString, stringLength, failureFunction,
                 loopCounter, bestOffset>>

\* The inner loop walks the failure chain; the outer loop has run past the
\* end of the string so the modulo index reaches back around.
InnerCompare ==
  /\ step = "innerCompare"
  /\ LET candidateChar ==
         inputString[(loopCounter - patternIndex) % stringLength]
       curChar == inputString[loopCounter % stringLength]
     IN /\ curChar # candidateChar
        /\ patternIndex # Undefined
        /\ step' = "postCompare"
        /\ UNCHANGED <<failureFunction>>
        /\ IF curChar < candidateChar
             THEN bestOffset' = loopCounter % stringLength
             ELSE bestOffset' = bestOffset
        /\ patternIndex' = patternIndex
        /\ loopCounter' = loopCounter
        /\ inputString' = inputString
        /\ stringLength' = stringLength
  /\ UNCHANGED <<step>>

PostCompare ==
  /\ step = "postCompare"
  /\ LET candidateChar ==
         inputString[(loopCounter - patternIndex) % stringLength]
       curChar == inputString[loopCounter % stringLength]
     IN /\ curChar # candidateChar
        /\ patternIndex = Undefined
        /\ step' = "increment"
        /\ UNCHANGED <<failureFunction>>
        /\ IF curChar < candidateChar
             THEN bestOffset' = loopCounter % stringLength
             ELSE bestOffset' = bestOffset
        /\ patternIndex' = patternIndex
        /\ loopCounter' = loopCounter
        /\ inputString' = inputString
        /\ stringLength' = stringLength
  /\ UNCHANGED <<step>>

\* Extending the match by one, or resetting the failure function entry.
FollowChain ==
  /\ step = "postCompare"
  /\ LET candidateChar ==
         inputString[(loopCounter - patternIndex) % stringLength]
       curChar == inputString[loopCounter % stringLength]
     IN /\ curChar # candidateChar
        /\ patternIndex = Undefined
        /\ step' = "increment"
        /\ failureFunction' = [failureFunction EXCEPT
                                 ![loopCounter] =
                                   IF curChar = candidateChar
                                     THEN IF patternIndex = Undefined
                                           THEN 1
                                           ELSE patternIndex + 1
                                     ELSE Undefined]
        /\ IF curChar < candidateChar
             THEN bestOffset' = loopCounter % stringLength
             ELSE bestOffset' = bestOffset
        /\ patternIndex' = patternIndex
        /\ loopCounter' = loopCounter
        /\ inputString' = inputString
        /\ stringLength' = stringLength
  /\ UNCHANGED <<step>>

Increment ==
  /\ step = "postCompare"
  /\ loopCounter' = loopCounter + 1
  /\ step' = "outerCheck"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex,
                 bestOffset>>

Halted == step = "halted"

Terminate ==
  /\ step \in {"postCompare", "increment"}
  /\ step' = "halted"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex,
                 loopCounter, bestOffset>>

Next == OuterCheck \/ FailureLookup \/ InnerCompare \/ FollowChain
        \/ PostCompare \/ Increment \/ Terminate

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Terminate)

TypeInvariant == TypeOK

\* The rotation at the recorded offset must compare less than or equal to
\* every other rotation; the offset is the smallest one among equal ones.
Correctness ==
  /\ \A i \in 1..(stringLength - 1) :
       \/ Rotate(inputString, bestOffset) <= Rotate(inputString, i)
       \/ Rotate(inputString, bestOffset) # Rotate(inputString, i) => bestOffset < i

Termination == Halted

====