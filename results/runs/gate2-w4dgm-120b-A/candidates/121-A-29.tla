---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

ZSequences == Sequences
\* CharacterSet replaces Nat from Naturals, so it may be any finite subset of Nat
\* and keep EXTENDS Naturals for the rest of the module.

VARIABLES inputString, length, failureFunction, matchIdx, loopCounter, bestOffset, pc

vars == <<inputString, length, failureFunction, matchIdx, loopCounter, bestOffset, pc>>

MaxLength == 2
Sentinel == 99

Corpus == {s \in ZSequences.Seq(CharacterSet) : Len(s) <= MaxLength}

TypeInvariant ==
    /\ inputString \in Corpus
    /\ length = Len(inputString)
    /\ failureFunction \in [0..(2 * MaxLength) -> 0..(2 * MaxLength) \cup {Sentinel}]
    /\ matchIdx \in 0..(2 * MaxLength) \cup {Sentinel}
    /\ loopCounter \in 0..(2 * MaxLength)
    /\ bestOffset \in 0..(length - 1)
    /\ pc \in {"outer", "init", "post", "final"}

\* The lexicographically-minimal rotation is at bestOffset: no other rotation
\* is strictly smaller, and equal rotations are broken by the smallest shift.
Correctness ==
    /\ \A i \in 0..(length - 1) : ZSequences.SubSeq(inputString, bestOffset, length - 1) ^ ZSequences.SubSeq(inputString, 0, bestOffset - 1)
                               <= ZSequences.SubSeq(inputString, i, length - 1) ^ ZSequences.SubSeq(inputString, 0, i - 1)
    /\ (\A i \in 0..(length - 1) :
          (ZSequences.SubSeq(inputString, bestOffset, length - 1) ^ ZSequences.SubSeq(inputString, 0, bestOffset - 1)
             = ZSequences.SubSeq(inputString, i, length - 1) ^ ZSequences.SubSeq(inputString, 0, i - 1))
             => bestOffset <= i)

\* The outer loop walks the double string, which covers the wrap-around.
Init ==
    /\ \E s \in Corpus : inputString = s
    /\ length = Len(inputString)
    /\ failureFunction = [i \in 0..(2 * MaxLength) |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outer"

LoopCheck ==
    /\ pc = "outer"
    /\ pc' = IF loopCounter < 2 * length THEN "init" ELSE "final"
    /\ UNCHANGED <<inputString, length, failureFunction, matchIdx, loopCounter, bestOffset>>

FailureLookup ==
    /\ pc = "init"
    /\ matchIdx' = failureFunction[loopCounter - bestOffset]
    /\ pc' = "inner"
    /\ UNCHANGED <<inputString, length, failureFunction, loopCounter, bestOffset>>

\* The inner loop walks through the matching band.
InnerLoop ==
    /\ pc = "inner"
    /\ LET cur == inputString[(loopCounter % length) + 1] + 1 IN
       LET cand == inputString[((bestOffset + loopCounter) % length) + 1] + 1 IN
         IF cur # cand /\ matchIdx # Sentinel THEN pc' = "inner"
         ELSE pc' = "post"
    /\ UNCHANGED <<inputString, length, failureFunction, matchIdx, loopCounter, bestOffset>>

UpdateOnLess ==
    /\ pc = "post"
    /\ LET cur == inputString[(loopCounter % length) + 1] + 1 IN
       LET cand == inputString[((bestOffset + loopCounter) % length) + 1] + 1 IN
         IF cur < cand THEN bestOffset' = (loopCounter + bestOffset) % length
         ELSE bestOffset' = bestOffset
    /\ UNCHANGED <<inputString, length, failureFunction, matchIdx, loopCounter, pc>>

FollowFailure ==
    /\ pc = "post"
    /\ failureFunction' = [failureFunction EXCEPT ![loopCounter - bestOffset] = IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1]
    /\ pc' = "post2"
    /\ UNCHANGED <<inputString, length, matchIdx, loopCounter, bestOffset>>

PostComparison ==
    /\ pc = "post2"
    /\ LET cur == inputString[(loopCounter % length) + 1] + 1 IN
       LET cand == inputString[((bestOffset + loopCounter) % length) + 1] + 1 IN
         IF cur < cand /\ matchIdx = Sentinel THEN bestOffset' = (loopCounter + bestOffset) % length
         ELSE bestOffset' = bestOffset
    /\ pc' = "next"
    /\ UNCHANGED <<inputString, length, failureFunction, matchIdx, loopCounter>>

IncrementLoop ==
    /\ pc = "next"
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<inputString, length, failureFunction, matchIdx, bestOffset>>

Stall ==
    /\ pc = "final"
    /\ pc' = pc
    /\ UNCHANGED <<inputString, length, failureFunction, matchIdx, loopCounter, bestOffset>>

Next ==
    \/ LoopCheck \/ FailureLookup \/ InnerLoop \/ UpdateOnLess
    \/ FollowFailure \/ PostComparison \/ IncrementLoop \/ Stall

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "final")

====