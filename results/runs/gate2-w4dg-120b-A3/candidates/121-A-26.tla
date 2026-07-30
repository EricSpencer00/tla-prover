---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences, ZSequences

\* The alphabet is a finite subset of the naturals; the model checks only
\* strings over this finite alphabet, which keeps the state space finite.
CONSTANTS CharacterSet

\* The sentinel marks an undefined entry in the failure function.
FreeEntry == -1
MaxStringLen == 3
MaxLoops == 3

VARIABLES str, len, failFn, pi, loopCtr, bestOff, pc

vars == <<str, len, failFn, pi, loopCtr, bestOff, pc>>

TypeOK ==
  /\ str \in Seq(CharacterSet)
  /\ len = Len(str)
  /\ failFn \in [0..(2*MaxStringLen - 1) -> {FreeEntry} \cup (0..MaxStringLen)]
  /\ pi \in {FreeEntry} \cup (0..MaxStringLen)
  /\ loopCtr \in 0..MaxLoops
  /\ bestOff \in 0..MaxStringLen
  /\ pc \in {"Outer", "Lookup", "Inner", "UpdateBest", "FollowFail",
             "PostCompare", "NextOuter", "Terminated"}

Init ==
  /\ \E s \in Seq(CharacterSet) : str' = s
  /\ len' = Len(str)
  /\ failFn' = [i \in 0..(2*MaxStringLen - 1) |-> FreeEntry]
  /\ pi' = FreeEntry
  /\ loopCtr' = 1
  /\ bestOff' = 0
  /\ pc' = "Outer"

OuterCheck ==
  /\ pc = "Outer"
  /\ IF loopCtr < 2 * MaxStringLen
     THEN pc' = "Lookup"
     ELSE pc' = "Terminated"
  /\ UNCHANGED <<str, len, failFn, pi, loopCtr, bestOff>>

LookupFailure ==
  /\ pc = "Lookup"
  /\ pi' = failFn[(loopCtr - 1 + bestOff) % MaxStringLen]
  /\ pc' = "Inner"
  /\ UNCHANGED <<str, len, failFn, loopCtr, bestOff>>

\* The inner compare loop walks the failure function chain until the chars
\* differ or the chain ends (pi = FreeEntry). The pc label decides the
\* branch rather than a guard, so the model explores both outcomes when
\* the chars are equal.
InnerCompare ==
  /\ pc = "Inner"
  /\ (pi # FreeEntry /\ str[(loopCtr + bestOff) % MaxStringLen + 1]
                         # str[(loopCtr + pi) % MaxStringLen + 1])
       \/ (pi = FreeEntry)
     /\ pc' = "UpdateBest"
  /\ (~(pi # FreeEntry /\ str[(loopCtr + bestOff) % MaxStringLen + 1]
                          # str[(loopCtr + pi) % MaxStringLen + 1])
        /\ pi # FreeEntry)
     /\ pc' = "FollowFail"
  /\ UNCHANGED <<str, len, failFn, pi, loopCtr, bestOff>>

UpdateBest ==
  /\ pc = "UpdateBest"
  /\ str[(loopCtr + bestOff) % MaxStringLen + 1]
       < str[(loopCtr + pi) % MaxStringLen + 1]
  /\ pi # FreeEntry
  /\ bestOff' = loopCtr + bestOff
  /\ pc' = "FollowFail"
  /\ UNCHANGED <<str, len, failFn, pi, loopCtr>>

FollowFailure ==
  /\ pc = "FollowFail"
  /\ pi # FreeEntry
  /\ pi' = failFn[pi]
  /\ pc' = "Lookup"
  /\ UNCHANGED <<str, len, failFn, loopCtr, bestOff>>

\* After the inner loop fails to match (pi = FreeEntry) the algorithm
\* must still check whether the current character is smaller, and
\* must reset or extend the failure function entry for the position.
PostComparison ==
  /\ pc = "PostCompare"
  /\ IF (pi = FreeEntry
         /\ str[(loopCtr + bestOff) % MaxStringLen + 1]
              < str[(loopCtr + pi) % MaxStringLen + 1])
        /\ pi # FreeEntry
        /\ bestOff' = loopCtr + bestOff
     ELSE bestOff' = bestOff
  /\ failFn' = [failFn EXCEPT ![(loopCtr - 1 + bestOff) % MaxStringLen] =
                 IF pi = FreeEntry THEN FreeEntry ELSE pi + 1]
  /\ pc' = "NextOuter"
  /\ UNCHANGED <<str, len, pi, loopCtr>>

NextOuter ==
  /\ pc = "NextOuter"
  /\ loopCtr' = loopCtr + 1
  /\ pc' = "Outer"
  /\ UNCHANGED <<str, len, failFn, pi, bestOff>>

StallTerminated ==
  /\ pc = "Terminated"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ LookupFailure \/ InnerCompare
  \/ UpdateBest \/ FollowFailure \/ PostComparison
  \/ NextOuter \/ StallTerminated

Fairness == WF_vars(OuterCheck) /\ WF_vars(LookupFailure)
           /\ WF_vars(InnerCompare) /\ WF_vars(UpdateBest)
           /\ WF_vars(FollowFailure) /\ WF_vars(PostComparison)
           /\ WF_vars(NextOuter) /\ WF_vars(StallTerminated)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Correctness: the rotation at the best offset is no larger than any
\* other rotation, and equal rotations resolve to the smallest shift.
Correctness ==
  /\ pc = "Terminated"
  /\ \A i \in 1..MaxStringLen :
       RotateAt(bestOff) <= RotateAt(i)
  /\ \A i \in 1..MaxStringLen :
       (RotateAt(bestOff) = RotateAt(i)) => bestOff <= i

RotateAt(off) == SubSeq(str, off + 1, MaxStringLen) ^ SubSeq(str, 1, off)

Properties == Spec => <>(pc = "Terminated")

====