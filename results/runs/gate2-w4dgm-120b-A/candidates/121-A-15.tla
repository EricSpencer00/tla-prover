---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

(* A circular string (viewed by index modulo its length) is processed by *)
(* Booth's linear-time lexicographically-least rotation algorithm.  The *)
(* input string is chosen nondeterministically from all zero-indexed      *)
(* sequences over the character set.  The failure function is a KMP-style  *)
(* back-pointer; the algorithm walks the string up to twice its length to  *)
(* handle the wrap-around implicitly.  Upon termination the best rotation *)
(* offset yields the lexicographically-minimal rotation.                   *)

CONSTANTS CharacterSet

Sentinel == 0

\* A zero-indexed string over the character set (the corpus is all such).
Corpus == UNION {[Chars -> CharacterSet] : Chars \in [1..Cardinality(CharacterSet)] -> CharacterSet}

VARIABLES inputString, n, fail, pattern, loopCtr, bestOffset, pc

vars == <<inputString, n, fail, pattern, loopCtr, bestOffset, pc>>

TypeInvariant ==
    /\ inputString \in Corpus
    /\ n = Len(inputString)
    /\ fail \in [0..2*n -> 0..(2*n + 1)]
    /\ pattern \in 0..(2*n + 1)
    /\ loopCtr \in 1..(2*n)
    /\ bestOffset \in 0..(n - 1)
    /\ pc \in {"outerCheck", "lookup", "compare", "updateBest", "follow", "postCompare", "done"}

Init ==
    /\ \E s \in Corpus : inputString = s
    /\ n = Len(inputString)
    /\ fail = [i \in 0..(2*n) |-> Sentinel]
    /\ pattern = Sentinel
    /\ loopCtr = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCtr < 2 * n THEN pc' = "lookup" ELSE pc' = "done"
    /\ UNCHANGED <<inputString, n, fail, pattern, loopCtr, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ fail' = [fail EXCEPT ![loopCtr] = fail[bestOffset + loopCtr]]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, n, pattern, loopCtr, bestOffset>>

\* Compare the character at loopCtr (mod n) with the one at the candidate.
\* If they differ and the pattern index is set, the inner loop continues.
Compare ==
    /\ pc = "compare"
    /\ inputString[(loopCtr % n) + 1] # inputString[(bestOffset + loopCtr) % n + 1]
    /\ \/ pattern # Sentinel
       \/ (pattern = Sentinel /\ pc' = "postCompare")
    /\ pc' = IF pattern # Sentinel THEN "compare" ELSE pc
    /\ UNCHANGED <<inputString, n, fail, pattern, loopCtr, bestOffset>>

UpdateBest ==
    /\ pc = "compare"
    /\ inputString[(loopCtr % n) + 1] < inputString[(bestOffset + loopCtr) % n + 1]
    /\ bestOffset' = (bestOffset + loopCtr) % n
    /\ pc' = "follow"
    /\ UNCHANGED <<inputString, n, fail, pattern, loopCtr>>

\* Follow the failure-function chain (or cut it off with the sentinel).
Follow ==
    /\ pc = "follow"
    /\ pattern' = fail[bestOffset + loopCtr]
    /\ pc' = "postCompare"
    /\ UNCHANGED <<inputString, n, fail, loopCtr, bestOffset>>

PostCompare ==
    /\ pc = "postCompare"
    /\ inputString[(loopCtr % n) + 1] # inputString[(bestOffset + loopCtr) % n + 1]
    /\ pattern = Sentinel
    /\ \/ (IF inputString[(loopCtr % n) + 1] < inputString[(bestOffset + loopCtr) % n + 1]
            THEN bestOffset' = (bestOffset + loopCtr) % n
            ELSE UNCHANGED bestOffset)
       /\ fail' = [fail EXCEPT ![bestOffset + loopCtr] = Sentinel]
    /\ pc' = "next"
    /\ UNCHANGED <<inputString, n, pattern, loopCtr>>

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ Compare
    \/ UpdateBest
    \/ Follow
    \/ PostCompare
    \/ (pc = "next" /\ loopCtr' = loopCtr + 1 /\ pc' = "outerCheck" /\ UNCHANGED <<inputString, n, fail, pattern, bestOffset>>)
    \/ (pc = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

\* Correctness: the rotation at the best offset is lexicographically <= all
\* others, and among equal rotations it has the smallest shift.
Correctness ==
    /\ \A i \in 0..(n - 1) : LexLe([k \in 0..(n - 1) |-> inputString[(bestOffset + k) % n + 1]],
                                   [k \in 0..(n - 1) |-> inputString[(i + k) % n + 1]])
    /\ \A i \in 0..(n - 1) : (LexEqual([k \in 0..(n - 1) |-> inputString[(bestOffset + k) % n + 1]],
                                         [k \in 0..(n - 1) |-> inputString[(i + k) % n + 1]]) => bestOffset <= i)

Termination == <>(pc = "done")

====