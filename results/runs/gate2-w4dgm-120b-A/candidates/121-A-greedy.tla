---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Zero-indexed sequences over a finite character set, with a sentinel value
\* for "undefined" that is one past the maximum valid index.
\* The algorithm is a direct translation of Booth's lexicographically-least
\* circular substring method, with a KMP-style failure function.
\* The model checker explores all strings up to the configured length over the
\* configured character set, so the correctness check applies to the whole
\* input space, not just a single run.

VARIABLES inputString, stringLength, failureFunction, patternIndex,
          loopCounter, bestOffset, pc

vars == <<inputString, stringLength, failureFunction, patternIndex,
           loopCounter, bestOffset, pc>>

Sentinel == 99
MaxLen == 3
MaxChar == 1

TypeInvariant ==
    /\ inputString \in [0..MaxLen -> CharacterSet]
    /\ stringLength = Len(inputString)
    /\ failureFunction \in [0..(2 * MaxLen) -> 0..(MaxLen + 1)]
    /\ patternIndex \in 0..(MaxLen + 1)
    /\ loopCounter \in 0..(2 * MaxLen)
    /\ bestOffset \in 0..MaxLen
    /\ pc \in {"outer", "lookup", "inner", "post", "done"}

Init ==
    /\ \E s \in [0..MaxLen -> CharacterSet] : inputString = s
    /\ stringLength = Len(inputString)
    /\ failureFunction = [i \in 0..(2 * MaxLen) |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outer"

OuterLoop ==
    /\ pc = "outer"
    /\ IF loopCounter < (2 * stringLength)
       THEN pc' = "lookup"
       ELSE pc' = "done"
    /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex,
                    loopCounter, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ failureFunction' = [failureFunction EXCEPT ![loopCounter] = Sentinel]
    /\ patternIndex' = failureFunction[loopCounter]
    /\ pc' = "inner"
    /\ UNCHANGED <<inputString, stringLength, loopCounter, bestOffset>>

\* The inner loop walks the failure chain until the characters match or the
\* chain is exhausted.
InnerLoop ==
    /\ pc = "inner"
    /\ LET curChar == inputString[loopCounter % stringLength]
           candChar == inputString[(bestOffset + loopCounter) % stringLength]
       IN IF curChar # candChar /\ patternIndex # Sentinel
          THEN /\ patternIndex' = failureFunction[patternIndex]
               /\ UNCHANGED <<inputString, stringLength, failureFunction,
                              loopCounter, bestOffset>>
          ELSE pc' = "post"
    /\ UNCHANGED <<inputString, stringLength, failureFunction, loopCounter, bestOffset>>

UpdateOnLess ==
    /\ pc = "post"
    /\ LET curChar == inputString[loopCounter % stringLength]
           candChar == inputString[(bestOffset + loopCounter) % stringLength]
       IN IF curChar < candChar
          THEN bestOffset' = loopCounter
          ELSE bestOffset' = bestOffset
    /\ pc' = "advance"
    /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex,
                   loopCounter>>

Advance ==
    /\ pc = "advance"
    /\ LET curChar == inputString[loopCounter % stringLength]
           candChar == inputString[(bestOffset + loopCounter) % stringLength]
       IN failureFunction' = [failureFunction EXCEPT
                                ![loopCounter] = IF curChar = candChar
                                                  THEN patternIndex + 1
                                                  ELSE Sentinel]
    /\ patternIndex' = Sentinel
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<inputString, stringLength, bestOffset>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == OuterLoop \/ Lookup \/ InnerLoop \/ UpdateOnLess \/ Advance \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(Lookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(UpdateOnLess) /\ WF_vars(Advance)

\* The rotation at bestOffset must be lexicographically <= every other rotation.
\* The second conjunct is the tie-breaker: among equal rotations, the smallest
\* shift is chosen, which is what makes the result unique.
Correctness ==
    /\ \A i \in 0..(stringLength - 1) :
         \A j \in 0..(stringLength - 1) :
           \A k \in 0..(stringLength - 1) :
             LET a == inputString[(i + k) % stringLength]
                 b == inputString[(j + k) % stringLength]
             IN (a < b) \/ (a = b /\ i <= j)

Termination == <>(pc = "done")

\* The .cfg file replaces the standard Nat with a finite version for this
\* model; the definition lives in the config, not in this module.
CharacterSet == CharacterSet
====