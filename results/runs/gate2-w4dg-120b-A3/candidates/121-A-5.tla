---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

\* The zero-indexed sequence operators are pulled from the standard module
\* under a new name so the model avoids the built-in NATURAL numbers range.
[ZSequences]CharacterSet

CONSTANT CharacterSet

\* The input string is a concrete sequence of characters from CharacterSet.
\* The length of the sequence determines the valid indexing range, and
\* the failure function is sized against twice that length.
Sequences == UNION {[1 .. n -> CharacterSet] : n \in Nat}
Sentinel == 0

VARIABLES inputString, stringLength, fail, matchIdx, loopCnt, bestOff, pc

vars == <<inputString, stringLength, fail, matchIdx, loopCnt, bestOff, pc>>

TypeInvariant ==
  /\ inputString \in Sequences
  /\ stringLength = Len(inputString)
  /\ fail \in [0 .. 2 * stringLength -> 0 .. 2 * stringLength]
  /\ matchIdx \in 0 .. 2 * stringLength
  /\ loopCnt \in 0 .. 2 * stringLength
  /\ bestOff \in 0 .. stringLength - 1
  /\ pc \in {"scan", "lookup", "refine", "follow", "reset"}

Init ==
  /\ inputString \in Sequences
  /\ stringLength = Len(inputString)
  /\ fail = [i \in 0 .. 2 * stringLength |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loopCnt = 1
  /\ bestOff = 0
  /\ pc = "scan"

\* Outer loop guard, modelling the doubled-iteration range.
CheckLoop ==
  /\ pc = "scan"
  /\ loopCnt < 2 * stringLength
  /\ pc' = "lookup"
  /\ UNCHANGED <<inputString, stringLength, fail, matchIdx, loopCnt, bestOff>>

Lookup ==
  /\ pc = "lookup"
  /\ matchIdx' = fail[loopCnt % stringLength + bestOff]
  /\ pc' = "refine"
  /\ UNCHANGED <<inputString, stringLength, fail, loopCnt, bestOff>>

\* The inner loop compares the candidate rotation with the current best.
Refine ==
  /\ pc = "refine"
  /\ IF inputString[loopCnt % stringLength + 1] # inputString[matchIdx % stringLength + 1]
       /\ matchIdx # Sentinel
       THEN pc' = "refine"
       ELSE pc' = "reset"
  /\ UNCHANGED <<inputString, stringLength, fail, matchIdx, loopCnt, bestOff>>

UpdateBest ==
  /\ inputString[loopCnt % stringLength + 1] < inputString[matchIdx % stringLength + 1]
  /\ bestOff' = loopCnt % stringLength
  /\ UNCHANGED <<inputString, stringLength, fail, matchIdx, loopCnt, pc>>

Follow ==
  /\ pc = "reset"
  /\ pc' = "follow"
  /\ matchIdx' = IF matchIdx = Sentinel THEN Sentinel ELSE fail[matchIdx]
  /\ UNCHANGED <<inputString, stringLength, fail, loopCnt, bestOff>>

\* The post-comparison step resets or extends the failure function.
Reset ==
  /\ pc = "follow"
  /\ matchIdx' = Sentinel
  /\ fail' = [fail EXCEPT ![loopCnt % stringLength + bestOff] =
                IF inputString[loopCnt % stringLength + 1] # inputString[matchIdx % stringLength + 1]
                  /\ matchIdx = Sentinel
                THEN Sentinel ELSE matchIdx + 1]
  /\ bestOff' = IF inputString[loopCnt % stringLength + 1] < inputString[matchIdx % stringLength + 1]
                  THEN loopCnt % stringLength ELSE bestOff
  /\ loopCnt' = loopCnt + 1
  /\ pc' = "scan"

Done ==
  /\ pc = "scan"
  /\ loopCnt >= 2 * stringLength
  /\ UNCHANGED vars

Stall ==
  /\ pc = "scan"
  /\ loopCnt >= 2 * stringLength
  /\ UNCHANGED vars

Next == CheckLoop \/ Lookup \/ Refine \/ UpdateBest \/ Follow \/ Reset \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(CheckLoop) /\ WF_vars(Lookup)
        /\ WF_vars(Follow) /\ WF_vars(Reset)

\* When the algorithm finishes, the rotation at bestOff is lexicographically
\* minimal among all rotations of the input string.
Correctness ==
  /\ loopCnt >= 2 * stringLength
  /\ \A k \in 0 .. stringLength - 1 :
       LET cand(i) == inputString[(i + k) % stringLength + 1] IN
       LexLe(cand, LEX, (inputString[(i + bestOff) % stringLength + 1] : i \in 0 .. stringLength-1))

LexLe(cand, LEX) == \A i \in 0 .. Len(cand) - 1 :
                     \A j \in 0 .. Len(cand) - 1 :
                       IF \A k \in 0 .. i - 1 : cand[k] = cand[k] THEN cand[i] <= cand[i] ELSE TRUE

Termination == <>(pc = "scan" /\ loopCnt >= 2 * stringLength)

====