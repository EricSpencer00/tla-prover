---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* A finite version of Nat, used by the ZSequences module this spec replaces.
Nat == 0 .. 1

\* An operation for indexing circular strings with an abstracted, pre-modulus index.
OnString(k, s) == s[(k % Len(s))]

VARIABLES inputString, stringLength, failFunc, patternIdx, loopCounter, bestOffset, pc
vars == <<inputString, stringLength, failFunc, patternIdx, loopCounter, bestOffset, pc>>

\* The sentinel marks an undefined entry in the failure function; it is outside the
\* valid index range so no valid lookup can ever return it.
Sentinel == stringLength + 2

TypeInvariant ==
    /\ inputString \in [0 .. 2 -> CharacterSet]
    /\ stringLength \in Nat
    /\ Len(inputString) = stringLength
    /\ failFunc \in [0 .. (stringLength * 2 - 1) -> 0 .. (stringLength + 1)]
    /\ patternIdx \in 0 .. (stringLength + 1)
    /\ loopCounter \in 0 .. (stringLength * 2)
    /\ bestOffset \in 0 .. (stringLength - 1)

Init ==
    /\ \E s \in [0 .. 2 -> CharacterSet] :
         inputString' = s
    /\ stringLength' = Len(inputString)
    /\ failFunc' = [i \in 0 .. (stringLength * 2 - 1) |-> Sentinel]
    /\ patternIdx' = Sentinel
    /\ loopCounter' = 1
    /\ bestOffset' = 0
    /\ pc' = "outer"

\* Outer loop over the doubled string; always eventually terminates.
Outer ==
    /\ loopCounter < (stringLength * 2)
    /\ pc' = "outer"
    /\ pc' = "lookup"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCounter, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ failFunc[loopCounter - 1] = Sentinel
    /\ pc' = "inner"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCounter, bestOffset>>

Inner ==
    /\ pc = "inner"
    /\ OnString(loopCounter, inputString) = OnString(bestOffset + patternIdx, inputString)
    /\ patternIdx < stringLength - 1
    /\ patternIdx' = patternIdx + 1
    /\ UNCHANGED <<inputString, stringLength, failFunc, loopCounter, bestOffset, pc>>

\* The comparison resolved: one direction is strictly better, the other worse.
Branch ==
    /\ pc = "inner"
    /\ OnString(loopCounter, inputString) # OnString(bestOffset + patternIdx, inputString)
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCounter, bestOffset, pc>>

UpdateOffset ==
    /\ pc = "inner"
    /\ OnString(loopCounter, inputString) < OnString(bestOffset + patternIdx, inputString)
    /\ bestOffset' = loopCounter % stringLength
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCounter, pc>>

FollowChain ==
    /\ pc = "inner"
    /\ failFunc[patternIdx] # Sentinel
    /\ patternIdx' = failFunc[patternIdx]
    /\ pc' = "post"
    /\ UNCHANGED <<inputString, stringLength, failFunc, loopCounter, bestOffset>>

\* No match chain left to follow (sentinel); resolve the final outcome.
FinalResolve ==
    /\ pc = "inner"
    /\ failFunc[patternIdx] = Sentinel
    /\ pc' = "post"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCounter, bestOffset>>

WriteBack ==
    /\ pc = "post"
    /\ failFunc' = [failFunc EXCEPT ![loopCounter] =
                      IF OnString(loopCounter, inputString) = OnString(bestOffset + patternIdx, inputString)
                      THEN patternIdx + 1 ELSE Sentinel]
    /\ UNCHANGED <<inputString, stringLength, patternIdx, loopCounter, bestOffset, pc>>

Increment ==
    /\ pc \in {"post", "outer"}
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, bestOffset>>

Done ==
    /\ pc = "outer"
    /\ loopCounter >= (stringLength * 2)
    /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Inner \/ Branch \/ UpdateOffset \/ FollowChain \/ FinalResolve \/ WriteBack \/ Increment \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(Branch) /\ WF_vars(UpdateOffset)
        /\ WF_vars(FollowChain) /\ WF_vars(FinalResolve) /\ WF_vars(WriteBack) /\ WF_vars(Increment)

\* The identified offset must describe the lexicographically smallest rotation of
\* the input string, comparing the whole rotated string against all others.
Correctness ==
    \A k \in 0 .. (stringLength - 1) :
        /\ OnString(bestOffset, inputString) <= OnString(k, inputString)
        /\ (OnString(bestOffset, inputString) = OnString(k, inputString) => bestOffset <= k)

Termination == WF_vars(Outer) /\ WF_vars(Lookup) /\ WF_vars(Inner) /\ WF_vars(Increment)

====