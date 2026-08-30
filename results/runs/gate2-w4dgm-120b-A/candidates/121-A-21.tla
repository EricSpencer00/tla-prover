---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Zero-indexed sequences over a finite character set; the model checker
\* bounds CharacterSet's size via the .cfg, so the state space stays finite.
ASSUME CharacterSet \subseteq Nat

\* The sentinel value that marks an undefined failure-function entry.
FailSentinel == 0

\* The failure function is indexed from 0 to twice the string length, so its
\* range covers the same interval and the sentinel stays just outside it.
FailRange(n) == 0..(n * 2)

VARIABLES str, len, fail, patIdx, outer, best, pc

vars == <<str, len, fail, patIdx, outer, best, pc>>

TypeInvariant ==
  /\ str \in Seq(CharacterSet)
  /\ len = Len(str)
  /\ fail \in [0..(len * 2) -> FailRange(len)]
  /\ patIdx \in FailRange(len)
  /\ outer \in 1..(len * 2)
  /\ best \in 0..(len - 1)
  /\ pc \in {"outerCheck", "failLookup", "innerLoop", "updateBest",
              "followFail", "postCompare", "final"}

\* Rotating a finite string one step left; the empty string is a valid test
\* case (it vacuously satisfies the minimal rotation property).
Rotate(s, k) == SubSeq(s, k + 1, Len(s)) \o SubSeq(s, 1, k)

\* Lexicographic comparison of two rotations of the same string.
LeqRotations(s, i, j) ==
  \/ \A k \in 1..Len(s) : s[i + k] = s[j + k]
  \/ \E k \in 1..Len(s) : /\ s[i + k] < s[j + k]
                          /\ \A h \in 1..(k - 1) : s[i + h] = s[j + h]

Init ==
  /\ \E w \in [1..Cardinality(CharacterSet) -> CharacterSet] :
       str = [i \in 1..Cardinality(CharacterSet) |-> w[i]]
  /\ len = Len(str)
  /\ fail = [i \in 0..(Cardinality(CharacterSet) * 2) |-> FailSentinel]
  /\ patIdx = FailSentinel
  /\ outer = 1
  /\ best = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF outer < len * 2 THEN pc' = "failLookup" ELSE pc' = "final"
  /\ UNCHANGED <<str, len, fail, patIdx, outer, best>>

FailLookup ==
  /\ pc = "failLookup"
  /\ patIdx' = fail[outer - 1]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, len, fail, outer, best>>

\* The inner loop walks the two rotations in lockstep; it exits when the
\* characters differ (a decision point) or the strings are exhausted.
InnerLoop ==
  /\ pc = "innerLoop"
  /\ IF str[(outer + best) % len] # str[(outer + patIdx) % len]
       /\ patIdx # FailSentinel
     THEN pc' = "postCompare"
     ELSE pc' = "postCompare"
  /\ UNCHANGED <<str, len, fail, patIdx, outer, best>>

UpdateBest ==
  /\ pc = "updateBest"
  /\ str[(outer + best) % len] < str[(outer + patIdx) % len]
  /\ best' = outer % len
  /\ pc' = "followFail"
  /\ UNCHANGED <<str, len, fail, patIdx, outer>>

FollowFail ==
  /\ pc = "followFail"
  /\ patIdx' = fail[patIdx]
  /\ pc' = "postCompare"
  /\ UNCHANGED <<str, len, fail, outer, best>>

PostCompare ==
  /\ pc = "postCompare"
  /\ IF str[(outer + best) % len] # str[(outer + patIdx) % len]
       /\ patIdx = FailSentinel
     THEN \/ (IF str[(outer + best) % len] < str[(outer + patIdx) % len]
              THEN best' = outer % len ELSE best' = best)
          /\ fail' = [fail EXCEPT ![outer] = FailSentinel]
     ELSE /\ fail' = [fail EXCEPT ![outer] = IF patIdx = FailSentinel
                                               THEN FailSentinel
                                               ELSE patIdx + 1]
          /\ UNCHANGED best
  /\ pc' = "increment"
  /\ UNCHANGED <<str, len, patIdx, outer>>

Increment ==
  /\ pc = "increment"
  /\ outer' = outer + 1
  /\ patIdx' = FailSentinel
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<str, len, fail, best>>

Final ==
  /\ pc = "final"
  /\ UNCHANGED vars

Next == OuterCheck \/ FailLookup \/ InnerLoop \/ UpdateBest \/ FollowFail
        \/ PostCompare \/ Increment \/ Final

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailLookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(UpdateBest) /\ WF_vars(FollowFail)
        /\ WF_vars(PostCompare) /\ WF_vars(Increment)

Correctness == LeqRotations(str, 1, best + 1)

Termination == <>(pc = "final")

====