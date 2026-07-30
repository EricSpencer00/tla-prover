---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* The Booth lexicographically-least circular substring algorithm.  This  *)
(* spec tracks the input string, a failure function, several loop indices  *)
(* and the best rotation offset found so far.  It returns the smallest     *)
(* rotation of the string, handling the wrap-around by iterating up to     *)
(* twice the string length (a doubled string).                             *)

CONSTANTS CharacterSet, Nat

AssumeSubset == /\ CharacterSet \subseteq Nat
               /\ \A a \in CharacterSet : a >= 0

Variables == <<inputSeq, seqLen, fail, matchIdx, outer, bestOffset, pc>>

Unused == 0

TypeInvariant ==
  /\ inputSeq \in Seq(CharacterSet)
  /\ seqLen = Len(inputSeq)
  /\ fail \in [0 .. 2 * seqLen] -> (0 .. 2 * seqLen) \cup {Unused}
  /\ matchIdx \in 0 .. 2 * seqLen \cup {Unused}
  /\ outer \in 1 .. 2 * seqLen
  /\ bestOffset \in 0 .. seqLen - 1
  /\ pc \in {"outerCheck", "lookupFail", "innerLoop", "updateBest",
             "followFail", "postCompare", "terminate", "stutter"}

Init ==
  /\ inputSeq \in Seq(CharacterSet)
  /\ seqLen = Len(inputSeq)
  /\ fail = [i \in 0 .. 2 * seqLen |-> Unused]
  /\ matchIdx = Unused
  /\ outer = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

\* Outer loop: bound is twice the string length (the doubled string).
OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF outer < 2 * seqLen THEN pc' = "lookupFail" ELSE pc' = "terminate"
  /\ UNCHANGED <<inputSeq, seqLen, fail, matchIdx, outer, bestOffset>>

LookupFail ==
  /\ pc = "lookupFail"
  /\ matchIdx' = fail[(outer - 1) % seqLen + bestOffset]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputSeq, seqLen, fail, outer, bestOffset>>

\* Inner loop: compare the character at the candidate rotation.
InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET cur == inputSeq[(outer % seqLen) + 1]
         cand == inputSeq[((outer - matchIdx) % seqLen) + 1]
     IN
       /\ IF cur # cand /\ matchIdx # Unused
          THEN pc' = "innerLoop"
          ELSE pc' = "postCompare"
       /\ matchIdx' = IF cur # cand /\ matchIdx # Unused THEN matchIdx ELSE matchIdx
  /\ UNCHANGED <<inputSeq, seqLen, fail, outer, bestOffset>>

UpdateBest ==
  /\ pc = "innerLoop"
  /\ matchIdx # Unused
  /\ inputSeq[(outer % seqLen) + 1] < inputSeq[((outer - matchIdx) % seqLen) + 1]
  /\ bestOffset' = outer % seqLen
  /\ UNCHANGED <<inputSeq, seqLen, fail, matchIdx, outer, pc>>

FollowFail ==
  /\ pc = "innerLoop"
  /\ matchIdx # Unused
  /\ matchIdx' = fail[matchIdx]
  /\ UNCHANGED <<inputSeq, seqLen, fail, outer, bestOffset, pc>>

\* Post-comparison: exit the inner loop, setting the failure function.
PostCompare ==
  /\ pc = "postCompare"
  /\ LET cur == inputSeq[(outer % seqLen) + 1]
         cand == inputSeq[((outer - matchIdx) % seqLen) + 1]
         newFail == IF cur # cand
                      THEN IF matchIdx = Unused
                             THEN Unused
                             ELSE matchIdx + 1
                      ELSE Unused
     IN
       /\ bestOffset' = IF cur # cand /\ matchIdx = Unused /\ cur < cand
                         THEN outer % seqLen ELSE bestOffset
       /\ fail' = [fail EXCEPT ![outer] = newFail]
  /\ UNCHANGED <<inputSeq, seqLen, matchIdx, outer, pc>>

IncrementOuter ==
  /\ pc = "postCompare"
  /\ outer' = outer + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputSeq, seqLen, fail, matchIdx, bestOffset>>

Terminate ==
  /\ pc = "terminate"
  /\ UNCHANGED <<inputSeq, seqLen, fail, matchIdx, outer, bestOffset, pc>>

Stutter ==
  /\ pc = "stutter"
  /\ UNCHANGED <<inputSeq, seqLen, fail, matchIdx, outer, bestOffset, pc>>

Next ==
  \/ OuterCheck \/ LookupFail \/ InnerLoop \/ UpdateBest \/ FollowFail
  \/ PostCompare \/ IncrementOuter \/ Terminate \/ Stutter

Spec ==
  /\ Init
  /\ [][Next]_Variables
  /\ WF_Variables(OuterCheck)
  /\ WF_Variables(LookupFail)
  /\ WF_Variables(InnerLoop)
  /\ WF_Variables(UpdateBest \/ FollowFail)
  /\ WF_Variables(PostCompare)
  /\ WF_Variables(IncrementOuter)

\* Correctness: bestOffset truly identifies the lexicographically-  *
\* minimal rotation, and ties are broken by the smallest shift.    *
Correctness ==
  /\ \A i \in 0 .. seqLen - 1 :
       LET rot(k) == SUBSEQ(inputSeq, k + 1, seqLen) \o SUBSEQ(inputSeq, 1, k)
       IN rot(bestOffset) <= rot(i)
  /\ \A i \in 0 .. seqLen - 1 :
       (rot(bestOffset) = rot(i)) => bestOffset <= i

Termination == <>(pc = "terminate")

====