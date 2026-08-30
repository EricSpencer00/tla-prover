---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, ZSequences

CONSTANTS CharacterSet

\* The sentinel value used to mean "undefined" for the failure function and
\* the pattern-match index; it is one past the maximum legal index.
Undefined == 3

VARIABLES inputString, stringLength, failure, patternIndex,
          loopCounter, bestOffset, pc

vars == <<inputString, stringLength, failure, patternIndex,
          loopCounter, bestOffset, pc>>

\* A circular string of length zero is allowed, so the corpus includes the
\* empty sequence; that edge case is what forces the bound on the PC chain.
Corpus == {s \in Seq(CharacterSet) : Len(s) <= 3}

TypeOK ==
    /\ inputString \in Corpus
    /\ stringLength = Len(inputString)
    /\ failure \in [0..(2 * stringLength) -> 0..(stringLength + 1)]
    /\ patternIndex \in 0..(stringLength + 1)
    /\ loopCounter \in 0..(2 * stringLength)
    /\ bestOffset \in 0..(stringLength - 1)
    /\ pc \in {"Outer", "Lookup", "Inner", "Update", "Chain", "Post", "Done"}

Init ==
    /\ \E s \in Corpus : inputString = s
    /\ stringLength = Len(inputString)
    /\ failure = [i \in 0..(2 * stringLength) |-> Undefined]
    /\ patternIndex = Undefined
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "Outer"

\* The algorithm runs in a linear sequence of labeled steps, with two
\* nested loops (an outer one over doubled string length, an inner one
\* that follows the failure chain). The PC variable is what keeps the
\* model checker honest about which step is executing next.
Outer ==
    /\ pc = "Outer"
    /\ IF loopCounter < (2 * stringLength)
       THEN pc' = "Lookup"
       ELSE pc' = "Done"
    /\ UNCHANGED <<inputString, stringLength, failure, patternIndex,
                   loopCounter, bestOffset>>

Lookup ==
    /\ pc = "Lookup"
    /\ patternIndex' = failure[loopCounter - bestOffset]
    /\ pc' = "Inner"
    /\ UNCHANGED <<inputString, stringLength, failure,
                   loopCounter, bestOffset>>

\* The inner comparison loop: two characters are compared, one from the
\* current position in the doubled string and one from the candidate
\* rotation. The loop body is entered only while the characters differ.
Inner ==
    /\ pc = "Inner"
    /\ (loopCounter % stringLength) # (bestOffset % stringLength)
    /\ (patternIndex # Undefined)
    /\ pc' = "Update"
    /\ UNCHANGED <<inputString, stringLength, failure, patternIndex,
                   loopCounter, bestOffset>>

Update ==
    /\ pc = "Update"
    /\ LET curChar == inputString[(loopCounter % stringLength) + 1]
         candChar == inputString[(bestOffset % stringLength) + 1]
    IN
        /\ IF curChar < candChar
           THEN bestOffset' = loopCounter % stringLength
           ELSE bestOffset' = bestOffset
    /\ patternIndex' = failure[patternIndex]
    /\ pc' = "Lookup"
    /\ UNCHANGED <<inputString, stringLength, failure,
                   loopCounter>>

\* Leaving the inner loop (patternIndex is the sentinel), the algorithm
\* re-checks the character comparison before deciding what to store in
\* the failure function for this position.
Post ==
    /\ pc = "Lookup"
    /\ patternIndex = Undefined
    /\ (loopCounter % stringLength) # (bestOffset % stringLength)
    /\ LET curChar == inputString[(loopCounter % stringLength) + 1]
         candChar == inputString[(bestOffset % stringLength) + 1]
    IN
        /\ IF curChar < candChar
           THEN bestOffset' = loopCounter % stringLength
           ELSE bestOffset' = bestOffset
    /\ failure' = [failure EXCEPT ![loopCounter] =
                       IF curChar = candChar THEN Undefined ELSE (patternIndex + 1)]
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "Outer"
    /\ UNCHANGED patternIndex

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Inner \/ Update \/ Post \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Outer) /\ WF_vars(Lookup)
                     /\ WF_vars(Inner) /\ WF_vars(Update) /\ WF_vars(Post)

\* Correctness: the rotation at bestOffset is no greater than any other
\* rotation of the input string, and among rotations that produce the
\* same sequence it has the smallest shift value -- exactly the
\* lexicographically-minimal rotation the Booth algorithm is meant to
\* find.
Correctness ==
    /\ pc = "Done"
    /\ \A i \in 1..(stringLength - 1) :
         LET rot1 == SubSeq(inputString, bestOffset + 1, stringLength - bestOffset)
                    \o SubSeq(inputString, 1, bestOffset)
             rot2 == SubSeq(inputString, i + 1, stringLength - i)
                    \o SubSeq(inputString, 1, i)
         IN
             \/ rot1 <= rot2
             \/ (rot1 = rot2 /\ i >= bestOffset)

Termination == (pc # "Done") ~> (pc = "Done")

\* The .cfg file overrides the standard Naturals.Nat with a finite
\* version -- a bounded version of the natural numbers -- so the model
\* checking state space stays finite. It is re-exported here under the
\* name the .cfg expects to find.
Nat == Cardinality(CharacterSet)

====