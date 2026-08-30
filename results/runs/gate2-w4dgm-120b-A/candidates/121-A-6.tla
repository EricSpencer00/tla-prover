---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

(* Bounded model of Booth's lexicographically-least circular substring     *)
(* algorithm.  The string is a zero-indexed sequence of characters drawn  from *)
(* a finite character set.  The algorithm builds a KMP-style failure table   *)
(* while scanning the string doubled.  Deterministic termination is       *)
(* captured as an absorbing final state.                                    *)

CONSTANTS CharacterSet

(* Sentinel value meaning "undefined" for an entry of the failure table.     *)
UNDEFINED == 0 - 1

VARIABLES str, strLen, failure, matchIdx, loopCounter, bestOffset pc

vars == <<str, strLen, failure, matchIdx, loopCounter, bestOffset, pc>>

TypeInvariant ==
  /\ str \in [0..(strLen - 1) -> CharacterSet]
  /\ strLen \in Nat
  /\ failure \in [0..(2 * strLen) -> (UNDEFINED \/ Nat)]
  /\ matchIdx \in (UNDEFINED \/ Nat)
  /\ loopCounter \in Nat
  /\ bestOffset \in Nat
  /\ pc \in {"outer", "lookup", "inner_loop", "post_compare", "done"}

Init ==
  /\ \E s \in Seq(CharacterSet) : str = [i \in 0..(Len(s) - 1) |-> s[i]]
  /\ strLen = Len(str)
  /\ failure = [i \in 0..(2 * strLen) |-> UNDEFINED]
  /\ matchIdx = UNDEFINED
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outer"

\* Outer loop: scan positions up to but not including twice the string length.
Outer ==
  /\ pc = "outer"
  /\ loopCounter < 2 * strLen
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, strLen, failure, matchIdx, loopCounter, bestOffset>>

\* Failure function lookup: read the table for the current position.
Lookup ==
  /\ pc = "lookup"
  /\ LET fval == failure[loopCounter + bestOffset] IN
       matchIdx' = fval
  /\ pc' = "inner_loop"
  /\ UNCHANGED <<str, strLen, failure, loopCounter, bestOffset>>

\* Compare the current character with the candidate from the failure index.
InnerLoop ==
  /\ pc = "inner_loop"
  /\ LET cur == str[loopCounter % strLen] IN
       LET cand == str[(loopCounter - matchIdx) % strLen] IN
         \/ (cur = cand /\ UNCHANGED <<failure, matchIdx, pc>>)
         \/ (cur # cand /\ matchIdx # UNDEFINED /\ pc' = "post_compare")
         \/ (cur # cand /\ matchIdx = UNDEFINED /\ pc' = "post_compare")
  /\ UNCHANGED <<str, strLen, loopCounter, bestOffset>>

\* Update the best rotation offset if the current character is smaller.
UpdateBest ==
  /\ pc \in {"inner_loop", "post_compare"}
  /\ LET cur == str[loopCounter % strLen] IN
       LET cand == str[(loopCounter - matchIdx) % strLen] IN
         IF cur # cand /\ cur < cand THEN bestOffset' = loopCounter % strLen
         ELSE UNCHANGED bestOffset
  /\ UNCHANGED <<str, strLen, failure, matchIdx, loopCounter, pc>>

\* Follow or reset the failure chain, then advance the outer loop.
Advance ==
  /\ pc \in {"inner_loop", "post_compare"}
  /\ failure' = [failure EXCEPT ![loopCounter + bestOffset] =
                    IF matchIdx = UNDEFINED THEN UNDEFINED ELSE matchIdx + 1]
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, strLen, matchIdx, bestOffset>>

Terminated ==
  /\ pc = "outer"
  /\ loopCounter >= 2 * strLen
  /\ pc' = "done"
  /\ UNCHANGED <<str, strLen, failure, matchIdx, loopCounter, bestOffset>>

Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Outer \/ Lookup \/ InnerLoop \/ UpdateBest \/ Advance \/ Terminated \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(UpdateBest) /\ WF_vars(Advance)

(* The offset found must indeed start the lexicographically smallest rotation. *)
Correctness ==
  /\ LET best == [i \in 0..(strLen - 1) |-> str[(bestOffset + i) % strLen]] IN
       \A o \in 0..(strLen - 1) :
         LET cand == [i \in 0..(strLen - 1) |-> str[(o + i) % strLen]] IN
           \/ \A i \in 0..(strLen - 1) : best[i] = cand[i]
           \/ \E i \in 0..(strLen - 1) : \A j \in 0..(i - 1) : best[j] = cand[j] /\ best[i] < cand[i]

\* The algorithm always eventually reaches its final absorbing state.
Termination == <>(pc = "done")
====