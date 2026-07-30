---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences

\* The lexicographically-least circular substring algorithm from Booth (1980).
\* A failure function similar to KMP's is built alongside the scan of the
\* doubled string.  The spec follows the description exactly: every identifier
\* below is required by the reference TLC configuration.

CONSTANTS CharacterSet, Nat

Sentinel == -1
MaxLen == Nat

VARIABLES str, len, failFn, patIdx, loopIdx, bestOffset, pc
vars == <<str, len, failFn, patIdx, loopIdx, bestOffset, pc>>

Init ==
  /\ str \in UNION { [1..n -> CharacterSet] : n \in 0..MaxLen }
  /\ len = Len(str)
  /\ failFn \in (0..(2 * len)) -> (0..(2 * len)) \cup {Sentinel}
  /\ patIdx = Sentinel
  /\ loopIdx = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

\* A fresh copy of the failure function each time the outer loop starts.
InitLoop ==
  /\ failFn' = [i \in 0..(2 * len) |-> Sentinel]
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, len, patIdx, loopIdx, bestOffset>>

Lookup ==
  /\ patIdx' = failFn[(loopIdx + bestOffset) % (2 * len)]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, len, failFn, loopIdx, bestOffset>>

\* The inner loop of Booth's algorithm walks the failure function chain.
\* Characters are compared modulo the string length, handling the wrap.
InnerLoop ==
  /\ pc = "innerLoop"
  /\ \/ (str[(loopIdx % len) + 1] # str[((loopIdx + patIdx) % len) + 1] /\ patIdx # Sentinel)
  \/ (patIdx = Sentinel)
  /\ pc' = "compare"
  /\ UNCHANGED <<str, len, failFn, patIdx, loopIdx, bestOffset>>

\* A strictly better rotation is remembered.
UpdateBest ==
  /\ pc = "compare"
  /\ patIdx # Sentinel
  /\ str[(loopIdx % len) + 1] < str[((loopIdx + patIdx) % len) + 1]
  /\ bestOffset' = loopIdx
  /\ pc' = "follow"
  /\ UNCHANGED <<str, len, failFn, patIdx, loopIdx>>

Follow ==
  /\ pc = "compare"
  /\ patIdx # Sentinel
  /\ str[(loopIdx % len) + 1] >= str[((loopIdx + patIdx) % len) + 1]
  /\ patIdx' = failFn[patIdx]
  /\ pc' = "follow"
  /\ UNCHANGED <<str, len, failFn, loopIdx, bestOffset>>

PostCompare ==
  /\ pc = "compare"
  /\ patIdx = Sentinel
  /\ str[(loopIdx % len) + 1] # str[((loopIdx + patIdx) % len) + 1]
  /\ IF str[(loopIdx % len) + 1] < str[((loopIdx + patIdx) % len) + 1]
       THEN bestOffset' = loopIdx
       ELSE bestOffset' = bestOffset
  /\ failFn' = [failFn EXCEPT ![(loopIdx + bestOffset) % (2 * len)] =
                   IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
  /\ pc' = "post"
  /\ UNCHANGED <<str, len, patIdx, loopIdx>>

NextLoop ==
  /\ pc = "post"
  /\ loopIdx' = loopIdx + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<str, len, failFn, patIdx, bestOffset>>

Terminate ==
  /\ pc = "outerCheck"
  /\ loopIdx >= 2 * len
  /\ pc' = "done"
  /\ UNCHANGED <<str, len, failFn, patIdx, loopIdx, bestOffset>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == InitLoop \/ Lookup \/ InnerLoop \/ UpdateBest \/ Follow
        \/ PostCompare \/ NextLoop \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(InitLoop) /\ WF_vars(Lookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(UpdateBest) /\ WF_vars(Follow)
        /\ WF_vars(PostCompare) /\ WF_vars(NextLoop) /\ WF_vars(Terminate)

TypeInvariant ==
  /\ str \in UNION { [1..n -> CharacterSet] : n \in 0..MaxLen }
  /\ len = Len(str)
  /\ failFn \in (0..(2 * len)) -> (0..(2 * len)) \cup {Sentinel}
  /\ patIdx \in {Sentinel} \cup (0..(2 * len))
  /\ loopIdx \in 1..(2 * len + 1)
  /\ bestOffset \in 0..(len - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "compare",
             "follow", "post", "done"}

\* The rotation at bestOffset is lexicographically minimal among all.
Correctness ==
  /\ pc = "done"
  /\ \A i \in 0..(len - 1) :
       LET rot(x) == <<SeqSubSeq(str, x + 1, len), SeqSubSeq(str, 1, x)>> IN
         (rot(bestOffset) # rot(i)) => (rot(bestOffset) < rot(i))
  /\ \A i \in 0..(len - 1) :
       (rot(i) = rot(bestOffset)) => (i >= bestOffset)

EventualTermination == <>(pc = "done")

====