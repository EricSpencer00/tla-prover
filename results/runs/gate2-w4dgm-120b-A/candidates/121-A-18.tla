---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

Sentinel == 0

VARIABLES inputStr, strLen, failure, kmpIndex, looper, best, pc

vars == <<inputStr, strLen, failure, kmpIndex, looper, best, pc>>

\* ZSequences version: zero-indexed strings, with a length operation and
\* modular indexing to model circularity.
Corpus == UNION { [1..n -> CharacterSet] : n \in Nat }

TypeInvariant ==
    /\ inputStr \in Corpus
    /\ strLen = Len(inputStr)
    /\ failure \in [0..2 * strLen -> 0..strLen]
    /\ kmpIndex \in 0..strLen
    /\ looper \in 1..(2 * strLen)
    /\ best \in 0..(strLen - 1)
    /\ pc \in {"outerCheck", "lookup", "compare", "updateBest",
               "followChain", "postCompare", "incrementPC", "halted"}

Init ==
    /\ \E s \in Corpus : inputStr = s
    /\ strLen = Len(inputStr)
    /\ failure = [i \in 0..(2 * strLen) |-> Sentinel]
    /\ kmpIndex = Sentinel
    /\ looper = 1
    /\ best = 0
    /\ pc = "outerCheck"

LoopCheck ==
    /\ pc = "outerCheck"
    /\ IF looper < 2 * strLen THEN pc' = "lookup" ELSE pc' = "halted"
    /\ UNCHANGED <<inputStr, strLen, failure, kmpIndex, looper, best>>

Lookup ==
    /\ pc = "lookup"
    /\ kmpIndex' = failure[best + looper]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputStr, strLen, failure, looper, best>>

\* Compare current character against the candidate from the failure chain.
Compare ==
    /\ pc = "compare"
    /\ LET a == inputStr[(looper % strLen) + 1]
           b == inputStr[((best + looper + (IF kmpIndex = Sentinel THEN 0 ELSE kmpIndex)) % strLen) + 1]
       IN
         /\ IF a = b THEN pc' = "postCompare"
            ELSE IF a < b THEN pc' = "updateBest"
            ELSE IF kmpIndex # Sentinel THEN pc' = "compare"
            ELSE pc' = "postCompare"
    /\ UNCHANGED <<inputStr, strLen, failure, kmpIndex, looper, best>>

UpdateBest ==
    /\ pc = "updateBest"
    /\ best' = looper
    /\ pc' = "compare"
    /\ UNCHANGED <<inputStr, strLen, failure, kmpIndex, looper>>

FollowChain ==
    /\ pc = "followChain"
    /\ kmpIndex' = failure[kmpIndex]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputStr, strLen, failure, looper, best>>

\* Reset or extend the failure function entry for the next iteration.
PostCompare ==
    /\ pc = "postCompare"
    /\ LET a == inputStr[(looper % strLen) + 1]
           b == inputStr[((best + looper + (IF kmpIndex = Sentinel THEN 0 ELSE kmpIndex)) % strLen) + 1]
           newval == IF a = b THEN (IF kmpIndex = Sentinel THEN 1 ELSE kmpIndex + 1) ELSE Sentinel
       IN
         /\ failure' = [failure EXCEPT ![best + looper] = newval]
         /\ kmpIndex' = Sentinel
    /\ pc' = "incrementPC"
    /\ UNCHANGED <<inputStr, strLen, looper, best>>

IncrementPC ==
    /\ pc = "incrementPC"
    /\ looper' = looper + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputStr, strLen, failure, kmpIndex, best>>

Halted ==
    /\ pc = "halted"
    /\ UNCHANGED vars

Next ==
    \/ LoopCheck
    \/ Lookup
    \/ Compare
    \/ UpdateBest
    \/ FollowChain
    \/ PostCompare
    \/ IncrementPC
    \/ Halted

Spec == Init /\ [][Next]_vars /\ WF_vars(Halted)

\* The best rotation is lexicographically <= every other rotation of the
\* input string, and among equal rotations it is the smallest shift.
Correctness ==
    /\ /\ (\A offset \in 1..(strLen - 1) :
              LET a == inputStr[(best % strLen) + 1]
                  b == inputStr[((best + offset) % strLen) + 1]
              IN a <= b)
       /\ (\A offset \in 1..(strLen - 1) :
              LET a == inputStr[(best % strLen) + 1]
                  b == inputStr[((best + offset) % strLen) + 1]
              IN a = b => best <= offset)

Termination == Eventually(pc = "halted")

====