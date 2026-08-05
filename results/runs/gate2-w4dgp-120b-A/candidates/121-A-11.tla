---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CharacterSet

\* The character set is now a finite subset of Nat, not Nat itself; the .cfg
\* replaces every Nat reference in this module with the finite set below.
ASSUME CharacterSet \subseteq (Nat \ {0})
MaxLen == 4
MinLen == 1
Doubled(n) == 2 * n
Sentinel == 0

VARIABLES inputString, strLen, failureFn, matchIdx, pos, bestOffset, pc
vars == <<inputString, strLen, failureFn, matchIdx, pos, bestOffset, pc>>

Corpus == UNION { [1..n -> CharacterSet] : n \in 0..MaxLen }

NextInRing(i, n) == (i % n) + 1

Init ==
    /\ inputString \in Corpus
    /\ strLen = Len(inputString)
    /\ failureFn \in [1..Doubled(strLen) -> {Sentinel} \cup (1..Doubled(strLen))]
    /\ \A i \in 1..Doubled(strLen) : failureFn[i] = Sentinel
    /\ matchIdx = Sentinel
    /\ pos = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF pos < Doubled(strLen)
       THEN /\ pc' = "lookup"
            /\ UNCHANGED <<inputString, strLen, failureFn, matchIdx, bestOffset>>
            /\ UNCHANGED pos
       ELSE /\ pc' = "terminated"
            /\ UNCHANGED <<inputString, strLen, failureFn, matchIdx, bestOffset>>
            /\ UNCHANGED pos
    /\ UNCHANGED <<inputString, strLen, failureFn, matchIdx, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ matchIdx' = failureFn[NextInRing(pos - bestOffset, strLen)]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<inputString, strLen, failureFn, bestOffset, pos>>

CharAt(i) == inputString[NextInRing(i, strLen)]

\* The inner loop is the KMP-like scanning; it only continues if a mismatch
\* is still pending a valid failure link to follow.
InnerLoop ==
    /\ pc = "innerLoop"
    /\ /\ CharAt(pos) # CharAt(NextInRing(bestOffset, strLen))
         /\ matchIdx # Sentinel
       \/ \/ CharAt(pos) = CharAt(NextInRing(bestOffset, strLen))
          \/ matchIdx = Sentinel
    /\ pc' = "postComparison"
    /\ UNCHANGED <<inputString, strLen, failureFn, matchIdx, bestOffset, pos>>

UpdateOnLess ==
    /\ CharAt(pos) < CharAt(NextInRing(bestOffset, strLen))
    /\ bestOffset' = pos - 1
    /\ UNCHANGED <<inputString, strLen, failureFn, matchIdx, pos, pc>>

FollowLink ==
    /\ pc = "innerLoop"
    /\ matchIdx' = failureFn[matchIdx]
    /\ UNCHANGED <<inputString, strLen, failureFn, bestOffset, pos>>
    /\ UNCHANGED pc

PostComparison ==
    /\ pc = "postComparison"
    /\ \/ (CharAt(pos) < CharAt(NextInRing(bestOffset, strLen))
           /\ bestOffset' = pos - 1)
       \/ (bestOffset' = bestOffset)
    /\ failureFn' = [failureFn EXCEPT ![NextInRing(pos - bestOffset, strLen)] =
                        IF CharAt(pos) = CharAt(NextInRing(bestOffset, strLen))
                        THEN Sentinel
                        ELSE matchIdx + 1]
    /\ pos' = pos + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, strLen, matchIdx>>

Stall ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ Lookup \/ InnerLoop \/ UpdateOnLess \/ FollowLink
    \/ PostComparison \/ Stall

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ inputString \in Corpus
    /\ strLen = Len(inputString)
    /\ failureFn \in [1..Doubled(strLen) -> {Sentinel} \cup (1..Doubled(strLen))]
    /\ matchIdx \in {Sentinel} \cup (1..Doubled(strLen))
    /\ pos \in 1..(Doubled(strLen) + 1)
    /\ bestOffset \in 0..MaxLen
    /\ pc \in {"outerCheck", "lookup", "innerLoop", "postComparison", "terminated"}

\* Upon termination, the identified rotation is the lexicographically
\* minimal one, and if several rotations produce the same sequence, it is
\* the one with the smallest shift (the smallest offset value).
Correctness ==
    /\ pc = "terminated"
    /\ \A i \in 0..(strLen - 1) :
         LET Rot(o) == <<CharAt(i + o) : o \in 0..(strLen - 1)>>
         IN Rot(bestOffset) <= Rot(i)
    /\ \A i \in 0..(strLen - 1) :
         (Rot(bestOffset) = Rot(i)) => (bestOffset <= i)

TerminationReached == <>(pc = "terminated")
====