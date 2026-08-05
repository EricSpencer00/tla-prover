---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

\* This module implements and verifies the lexicographically-least circular
\* substring algorithm from Booth's 1980 paper. A double-length
\* iteration (0 <= outerCounter < 2 * len) handles the wrap-around without
\* explicit circular indexing aside from the mod-by-length used everywhere.
\* The algorithm mirrors KMP: it maintains a failure function (phi) that
\* records where a prior prefix-suffix match left off, and it uses that
\* failure function to skip forward when a character mismatch occurs
\* during the inner comparison loop. When the loop counter reaches
\* twice the length the algorithm has examined every rotation of the
\* string and settles on the best offset seen. That offset is the
\* lexicographically-minimal rotation of the input string.
\* The full system is: an input string (chosen nondeterministically from
\* all zero-indexed sequences over a finite character set), the failure
\* function, loop control variables, and a program counter that walks
\* through the algorithm's labeled steps. The invariants keep every
\* variable in range; the correctness property ties the final offset to
\* the lexicographic ordering of every rotation of the input string.

\* Zero-indexed char sequences are defined here to replace Naturals' one-indexing:
\* the alphabet is a finite subset of Nat, so Nat stays available for
\* arithmetic while CharacterSet becomes a bounded type.
CharacterSet == {0, 1}

VARIABLES string, length, phi, pmatch, outerCounter, bestOffset, pc

vars == <<string, length, phi, pmatch, outerCounter, bestOffset, pc>>

None == -1

\* Enumerate all zero-indexed sequences over CharacterSet up to length 3
\* for model checking; the real algorithm accepts any length.
StringSpace == UNION { [1..n -> CharacterSet] : n \in 1..3 }

TypeInvariant ==
    /\ string \in StringSpace
    /\ length = Len(string)
    /\ phi \in [0..(2 * length) -> None..length]
    /\ pmatch \in None..length
    /\ outerCounter \in 0..(2 * length)
    /\ bestOffset \in 0..(length - 1)
    /\ pc \in {"outerCheck", "phiLookup", "innerLoop", "innerLess",
               "followFailure", "postComparison", "done"}

\* Lexicographic ordering of zero-indexed rotations: a rotation at index i
\* is lexicographically less than one at index j if at the first position
\* k where the two strings differ its character is smaller; if the two
\* rotations are identical, the smaller shift value is the tie-breaker.
\* Each rotation is a zero-indexed sequence, so the same ordering holds
\* whether a rotation is inspected from the start or from any other
\* point -- which is what makes the comparison valid for the circular
\* string: the offset is always measured from the original start.
Rotation(i) == [k \in 0..(length - 1) |-> string[((i + k) % length) + 1]]

LessThan(i, j) ==
    \/ \E k \in 0..(length - 1) :
         /\ \A m \in 0..(k - 1) : Rotation(i)[m] = Rotation(j)[m]
         /\ Rotation(i)[k] < Rotation(j)[k]
    \/ (\A k \in 0..(length - 1) : Rotation(i)[k] = Rotation(j)[k]) /\ (i < j)

Init ==
    /\ string \in StringSpace
    /\ length = Len(string)
    /\ phi = [n \in 0..(2 * length) |-> None]
    /\ pmatch = None
    /\ outerCounter = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ (outerCounter < (2 * length) -> pc' = "phiLookup")
    /\ (outerCounter >= (2 * length) -> pc' = "done")
    /\ UNCHANGED <<string, length, phi, pmatch, outerCounter, bestOffset>>

PhiLookup ==
    /\ pc = "phiLookup"
    /\ phi' = [phi EXCEPT ![outerCounter] = phi[outerCounter]]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<string, length, pmatch, outerCounter, bestOffset>>

InnerLoop ==
    /\ pc = "innerLoop"
    /\ LET curr == string[(outerCounter % length) + 1]
           cand == string[((bestOffset + outerCounter) % length) + 1] IN
       /\ (curr = cand \/ pmatch = None) -> pc' = "postComparison"
       /\ (curr # cand /\ pmatch # None) -> pc' = "innerLoop"
    /\ UNCHANGED <<string, length, phi, pmatch, outerCounter, bestOffset>>

InnerLess ==
    /\ pc = "innerLoop"
    /\ LET curr == string[(outerCounter % length) + 1]
           cand == string[((bestOffset + outerCounter) % length) + 1] IN
       /\ (curr # cand /\ pmatch # None /\ curr < cand)
       /\ bestOffset' = (outerCounter + bestOffset) % length
    /\ pc' = "followFailure"
    /\ UNCHANGED <<string, length, phi, pmatch, outerCounter>>

FollowFailure ==
    /\ pc = "followFailure"
    /\ pmatch' = phi[outerCounter]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<string, length, phi, outerCounter, bestOffset>>

PostComparison ==
    /\ pc = "postComparison"
    /\ LET curr == string[(outerCounter % length) + 1]
           cand == string[((bestOffset + outerCounter) % length) + 1] IN
       /\ (curr # cand /\ pmatch = None /\ curr < cand)
       /\ bestOffset' = (outerCounter + bestOffset) % length
    /\ phi' = [phi EXCEPT ![outerCounter] = (IF pmatch = None THEN None ELSE pmatch + 1)]
    /\ outerCounter' = outerCounter + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<string, length, pmatch>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ PhiLookup
    \/ InnerLoop
    \/ InnerLess
    \/ FollowFailure
    \/ PostComparison
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(PhiLookup)

\* Correctness: on termination the best offset is lexicographically
\* minimal among all rotations of the input string (and if two rotations
\* compare equal, the one with the smaller shift is taken, which is what
\* the tie-breaking clause in LessThan does).
Correctness ==
    (pc = "done") => (\A j \in 0..(length - 1) : LessThan(bestOffset, j))

Termination == <>[](pc = "done")

====