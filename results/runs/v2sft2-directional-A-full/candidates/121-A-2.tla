---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANT CharacterSet \* a finite subset of Nat, supplied by the .cfg
CONSTANT Nat

\*-----------------------------------------------------------------
\* Variables
\*-----------------------------------------------------------------
VARIABLES inputStr, strLen, failFunc, patIdx, loopCnt, bestOff, pc

\*-----------------------------------------------------------------
\* Type definitions (used only for the type invariant)
\*-----------------------------------------------------------------
SeqOfCharacter == { s \in Seq[CharacterSet] } \* zero-indexed sequence
FailVal == { Sentinel } \cup Nat \* failure function values
pcValues == {"Start", "OuterCheck", "FailLookup", "InnerComp",
             "UpdateBest", "FollowFail", "PostComp", "IncLoop", "Done"}

\*-----------------------------------------------------------------
\* Sentinel value for “undefined” in the failure function
\*-----------------------------------------------------------------
Sentinel == -1

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
Mod(i, n) == i % n

\* All indices that the failure function can hold (0 .. 2*strLen)
FailIndices == 0 .. 2 * strLen

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ inputStr \in SeqOfCharacter
    /\ strLen = Len(inputStr)
    /\ failFunc = [i \in FailIndices |-> Sentinel]
    /\ patIdx = Sentinel
    /\ loopCnt = 1
    /\ bestOff = 0
    /\ pc = "Start"

\*-----------------------------------------------------------------
\* Actions
\*-----------------------------------------------------------------
OuterCheck ==
    /\ pc = "Start"
    /\ loopCnt < 2 * strLen
    /\ pc' = "FailLookup"

\* Retrieve the failure function entry for the current position
FailLookup ==
    /\ pc = "FailLookup"
    /\ patIdx' = failFunc[Mod(loopCnt, 2 * strLen)]
    /\ pc' = "InnerComp"

\* Inner comparison loop: compare characters at (loopCnt) and (bestOff)
InnerComp ==
    /\ pc = "InnerComp"
    /\ loopCnt < 2 * strLen
    /\ IF Mod(loopCnt, strLen) = Mod(bestOff, strLen) THEN
           /\ pc' = "IncLoop"
      ELSE IF inputStr[Mod(loopCnt, strLen)] <
             inputStr[Mod(bestOff, strLen)] THEN
           /\ bestOff' = Mod(loopCnt, strLen)
           /\ pc' = "FollowFail"
      ELSE
           /\ pc' = "FollowFail"

\* Follow the failure function chain
FollowFail ==
    /\ pc = "FollowFail"
    /\ IF patIdx = Sentinel THEN
           /\ pc' = "PostComp"
      ELSE
           /\ patIdx' = failFunc[patIdx]
           /\ pc' = "InnerComp"

\* Post comparison step: update failure function and possibly best offset
PostComp ==
    /\ pc = "PostComp"
    /\ IF inputStr[Mod(loopCnt, strLen)] <
           inputStr[Mod(bestOff, strLen)] THEN
           /\ bestOff' = Mod(loopCnt, strLen)
      /\ IF patIdx = Sentinel THEN
           /\ failFunc' = [failFunc EXCEPT ![Mod(loopCnt, 2 * strLen)] = Sentinel]
      ELSE
           /\ failFunc' = [failFunc EXCEPT ![Mod(loopCnt, 2 * strLen)] = patIdx + 1]
      /\ pc' = "IncLoop"

\* Increment loop counter
IncLoop ==
    /\ pc = "IncLoop"
    /\ loopCnt' = loopCnt + 1
    /\ pc' = "OuterCheck"

\* Termination stutter after the loop has completed
Termination ==
    /\ pc = "OuterCheck"
    /\ loopCnt >= 2 * strLen
    /\ pc' = "Done"

\* Stuttering action to stay in the Done state
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<inputStr, strLen, failFunc, patIdx, loopCnt, bestOff, pc>>

\* Next-state relation
Next ==
    \/ OuterCheck
    \/ FailLookup
    \/ InnerComp
    \/ FollowFail
    \/ PostComp
    \/ IncLoop
    \/ Termination
    \/ Stutter

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<inputStr, strLen, failFunc, patIdx, loopCnt, bestOff, pc>>

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
TypeInvariant ==
    /\ inputStr \in SeqOfCharacter
    /\ strLen = Len(inputStr)
    /\ failFunc \in [FailIndices -> FailVal]
    /\ patIdx \in FailVal
    /\ loopCnt \in Nat
    /\ bestOff \in 0 .. strLen - 1
    /\ pc \in pcValues

Correctness ==
    \A i, j \in 0 .. strLen - 1 :
        (inputStr[(bestOff + i) % strLen] <= inputStr[(j + i) % strLen]) =>
            (bestOff <= j)

\*-----------------------------------------------------------------
\* Definitions for the .cfg (not part of the module but shown for clarity)
\*-----------------------------------------------------------------
\* DEFINE
\*     CharacterSet = 0..25   \* for example, lowercase letters
\*     Nat = Nat
\*     Init = Init
\* END DEFINE

====