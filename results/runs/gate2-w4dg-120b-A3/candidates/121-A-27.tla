---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet

VARIABLES input, n, failFn, failIdx, i, bestOff, pc
vars == <<input, n, failFn, failIdx, i, bestOff, pc>>

Sentinel == 0 - 1
MaxLen == 3
AllStrings == { s \in Seq(CharacterSet) : Len(s) <= MaxLen }
MaxI == 2 * MaxLen

TypeInvariant ==
  /\ input \in AllStrings
  /\ Len(input) = n
  /\ failFn \in [0..MaxI -> {Sentinel} \cup (0..MaxI)]
  /\ failIdx \in {Sentinel} \cup (0..MaxI)
  /\ i \in 1..MaxI
  /\ bestOff \in 0..n - 1
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "failureFollow", "postUpdate"}

Init ==
  /\ input \in AllStrings
  /\ n = Len(input)
  /\ failFn = [k \in 0..MaxI |-> Sentinel]
  /\ failIdx = Sentinel
  /\ i = 1
  /\ bestOff = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ i < MaxI
  /\ pc' = "lookup"
  /\ UNCHANGED <<input, n, failFn, failIdx, i, bestOff>>

Lookup ==
  /\ pc = "lookup"
  /\ failIdx' = failFn[(i - 1) % n + bestOff]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<input, n, failFn, i, bestOff>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ ((input[(i % n) + 1] # input[((i + failIdx) % n) + 1]) /\ (failIdx # Sentinel))
      => pc' = "failureFollow"
  /\ ((input[(i % n) + 1] = input[((i + failIdx) % n) + 1]) \/ (failIdx = Sentinel))
      => pc' = "postUpdate"
  /\ UNCHANGED <<input, n, failFn, failIdx, i, bestOff>>

FailureFollow ==
  /\ pc = "failureFollow"
  /\ failIdx' = failFn[failIdx]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<input, n, failFn, i, bestOff>>

PostUpdate ==
  /\ pc = "postUpdate"
  /\ LET cand == ((i + failIdx) % n) + 1
         cur == (i % n) + 1
         newOff == IF input[cur] < input[cand] THEN i % n ELSE bestOff
         newIdx == IF input[cur] = input[cand] /\ failIdx # Sentinel
                     THEN failIdx + 1 ELSE Sentinel
         newFail == IF (input[cur] # input[cand] /\ failIdx = Sentinel) /\ (newOff # bestOff)
                      THEN Sentinel ELSE newIdx
     IN
       /\ failFn' = [failFn EXCEPT ![i] = newFail]
       /\ bestOff' = newOff
  /\ i' = i + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<input, n, failIdx>>

LoopStep == Lookup \/ InnerLoop \/ FailureFollow \/ PostUpdate

Stall ==
  /\ pc = "outerCheck"
  /\ i >= MaxI
  /\ UNCHANGED vars

Next == OuterCheck \/ LoopStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep) /\ WF_vars(LoopStep)

Correctness ==
  /\ i = MaxI
  /\ \A j \in 0..n - 1 :
       LexLeq(Rotate(input, bestOff), Rotate(input, j))
  /\ \A j \in 0..n - 1 :
       (Rotate(input, j) = Rotate(input, bestOff)) => (j >= bestOff)

Termination == <>(pc = "outerCheck" /\ i >= MaxI)

====