---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* The smallest rotation is defined by lexicographic ordering on the
\* double-length iteration of the circular string.
\* The algorithm is Booth's linear-time method using a failure function
\* (like KMP) rather than a naïve quadratic pairwise rotation compare.

\* The spec is deliberately single-threaded: the program counter models
\* where control is, and every step below is guarded by it. The sequence
\* is bounded by both the character set size and the maximum length the
\* model checker is willing to explore.

VARIABLES inputStr, len, fail, pm, outer, bestOffset, pc

vars == <<inputStr, len, fail, pm, outer, bestOffset, pc>>

Corpora == UNION { [1..n -> CharacterSet] : n \in Nat }

Sentinel == 999
MaxLen == 3
MaxChar == 1

TypeInvariant ==
  /\ inputStr \in Corpora
  /\ len = Len(inputStr)
  /\ fail \in [0..2*MaxLen -> 0..MaxLen \cup {Sentinel}]
  /\ pm \in 0..MaxLen \cup {Sentinel}
  /\ outer \in 1..(2*MaxLen + 1)
  /\ bestOffset \in 0..MaxLen
  /\ pc \in {"c0", "c1", "c2", "c3", "c4", "c5", "c6", "done"}

Init ==
  /\ inputStr \in Corpora
  /\ len = Len(inputStr)
  /\ fail = [i \in 0..2*MaxLen |-> Sentinel]
  /\ pm = Sentinel
  /\ outer = 1
  /\ bestOffset = 0
  /\ pc = "c0"

\* c0: start of the outer loop test
OuterLoop ==
  /\ pc = "c0"
  /\ IF outer < 2*len + 1 THEN pc' = "c1" ELSE pc' = "done"
  /\ UNCHANGED <<inputStr, len, fail, pm, outer, bestOffset>>

\* c1: read the failure function entry for the current offset candidate
Lookup ==
  /\ pc = "c1"
  /\ pm' = fail[outer - bestOffset]
  /\ pc' = "c2"
  /\ UNCHANGED <<inputStr, len, fail, outer, bestOffset>>

\* c2: inner character comparison (these comments are the only place
\* the model's alignment with Booth's paper is explained)
CompareChars ==
  /\ pc = "c2"
  /\ LET
       curChar == inputStr[(outer % len) + 1]
       candChar == inputStr[((outer + pm + 1) % len) + 1]
     IN
       /\ IF curChar = candChar
            THEN pc' = "c6"
            ELSE IF pm # Sentinel
                 THEN pc' = "c3"
                 ELSE pc' = "c4"
  /\ UNCHANGED <<inputStr, len, fail, pm, outer, bestOffset>>

\* c3: found a strictly better rotation; record the smaller offset
UpdateBest ==
  /\ pc = "c3"
  /\ LET
       curChar == inputStr[(outer % len) + 1]
       candChar == inputStr[((outer + pm + 1) % len) + 1]
     IN
       /\ curChar < candChar
       /\ bestOffset' = outer
  /\ pc' = "c5"
  /\ UNCHANGED <<inputStr, len, fail, pm, outer>>

\* c4: no failure link left to chase, but the rotation was still better
UpdateBestNoFail ==
  /\ pc = "c4"
  /\ LET
       curChar == inputStr[(outer % len) + 1]
       candChar == inputStr[((outer + pm + 1) % len) + 1]
     IN
       /\ curChar < candChar
       /\ bestOffset' = outer
  /\ pc' = "c5"
  /\ UNCHANGED <<inputStr, len, fail, pm, outer>>

\* c5: advance the failure function (reset or extend the current match)
AdvanceFailure ==
  /\ pc = "c5"
  /\ fail' = [fail EXCEPT ![outer - bestOffset] =
                 IF pm = Sentinel THEN Sentinel ELSE pm + 1]
  /\ pc' = "c6"
  /\ UNCHANGED <<inputStr, len, pm, outer, bestOffset>>

\* c6: back to the outer loop test with the loop counter advanced
NextIteration ==
  /\ pc = "c6"
  /\ outer' = outer + 1
  /\ pc' = "c0"
  /\ UNCHANGED <<inputStr, len, fail, pm, bestOffset>>

\* done: the algorithm has finished; this is a terminal self-loop
Finished ==
  /\ pc = "done"
  /\ UNCHANGED vars

\* The usual TLA+ liveness trick: a no-op that keeps the model moving
Stall == Finished /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ Lookup \/ CompareChars \/ UpdateBest
  \/ UpdateBestNoFail \/ AdvanceFailure \/ NextIteration
  \/ Finished \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(NextIteration)

\* The second clause is the substantive one: on termination, the best
\* offset names the lexicographically smallest rotation of the input
\* (and minimal rotation is unique to the smallest shift among equals).
Correctness ==
  /\ pc = "done"
  /\ \A m \in 0..(len - 1) :
       LexicographicLeq(
         SubSeq(inputStr, bestOffset + 1, len) ^ SubSeq(inputStr, 1, bestOffset),
         SubSeq(inputStr, m + 1, len) ^ SubSeq(inputStr, 1, m))
  /\ \A m \in 0..(len - 1) :
       (LexicographicEq(
          SubSeq(inputStr, bestOffset + 1, len) ^ SubSeq(inputStr, 1, bestOffset),
          SubSeq(inputStr, m + 1, len) ^ SubSeq(inputStr, 1, m))
        => bestOffset <= m)

Termination == (pc # "done") ~> (pc = "done")

====