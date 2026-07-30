---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet, Nat

\* sentinel value for "undefined" entries of the failure function
UNDEFINED == 0

VARIABLES inputString, strLen, fail, patIdx, loopIdx, bestOffset, pc

vars == <<inputString, strLen, fail, patIdx, loopIdx, bestOffset, pc>>

\* The corpus is every possible zero-indexed sequence over CharacterSet
Corpus == {s \in Seq(CharacterSet) : Len(s) <= Nat}

Init ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ fail = [i \in 0..(2 * strLen) |-> UNDEFINED]
  /\ patIdx = UNDEFINED
  /\ loopIdx = 1
  /\ bestOffset = 0
  /\ pc = "outer_check"

\* Step 1: outer loop, stop once loopIdx reaches twice the length
OuterCheck ==
  /\ pc = "outer_check"
  /\ IF loopIdx < 2 * strLen
       THEN pc' = "func_lookup"
       ELSE pc' = "done"
  /\ UNCHANGED <<inputString, strLen, fail, patIdx, loopIdx, bestOffset>>

\* Step 2: retrieve the failure function entry for the current offset
FuncLookup ==
  /\ pc = "func_lookup"
  /\ patIdx' = fail[loopIdx - bestOffset]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, strLen, fail, loopIdx, bestOffset>>

\* Characters to compare, with wrap-around handled by modulo indexing
c1 == inputString[(loopIdx) % strLen]
c2 == inputString[(loopIdx - bestOffset) % strLen]

\* Step 3: inner loop -- characters differ and the failure chain has not
\* exhausted; otherwise exit to post-comparison
InnerLoop ==
  /\ pc = "compare"
  /\ (c1 /= c2 /\ patIdx # UNDEFINED)
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, strLen, fail, patIdx, loopIdx, bestOffset>>

\* Step 4: a strictly smaller character at the current position updates
\* the best rotation offset
UpdateBest ==
  /\ pc = "compare"
  /\ c1 # c2
  /\ patIdx # UNDEFINED
  /\ c1 < c2
  /\ bestOffset' = loopIdx
  /\ UNCHANGED <<inputString, strLen, fail, patIdx, loopIdx, pc>>

\* Step 5: follow the failure function chain
FollowChain ==
  /\ pc = "compare"
  /\ (c1 /= c2 /\ patIdx # UNDEFINED)
  /\ patIdx' = fail[patIdx]
  /\ UNCHANGED <<inputString, strLen, fail, loopIdx, bestOffset, pc>>

\* Step 6: post-comparison after the inner chain exhausted
PostCompare ==
  /\ pc = "compare"
  /\ c1 # c2
  /\ patIdx = UNDEFINED
  /\ LET newOffset ==
        IF c1 < c2 THEN loopIdx ELSE bestOffset
       entry ==
        IF c1 = c2 THEN UNDEFINED ELSE patIdx + 1
     IN /\ bestOffset' = newOffset
        /\ fail' = [fail EXCEPT ![loopIdx] = entry]
  /\ UNCHANGED <<inputString, strLen, patIdx, loopIdx, pc>>

\* Step 7: advance the outer loop counter and cycle back
LoopStep ==
  /\ pc \in {"compare", "post_compare"}
  /\ pc' = "outer_check"
  /\ loopIdx' = loopIdx + 1
  /\ UNCHANGED <<inputString, strLen, fail, patIdx, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == OuterCheck \/ FuncLookup \/ InnerLoop \/ UpdateBest \/ FollowChain
        \/ PostCompare \/ LoopStep \/ Done

\* The outer loop cycles only on progress, so strong fairness terminates it
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(OuterCheck)
  /\ SF_vars(FuncLookup)
  /\ SF_vars(LoopStep)

TypeInvariant ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ fail \in [0..(2 * strLen) -> (0..Nat) \cup {UNDEFINED}]
  /\ patIdx \in (0..Nat) \cup {UNDEFINED}
  /\ loopIdx \in 1..(2 * strLen)
  /\ bestOffset \in 0..(strLen - 1)
  /\ pc \in {"outer_check", "func_lookup", "compare", "post_compare", "done"}

\* Correctness: bestOffset names the lexicographically-minimal rotation, and
\* among equal rotations it is the smallest shift value.
Correctness ==
  /\ \A i \in 1..(strLen - 1) :
       LET rot(a) == << inputString[(a + j) % strLen] : j \in 0..(strLen - 1) >>
       IN rot(bestOffset) <= rot(i)
  /\ \A i \in 1..(strLen - 1) :
       (rot(bestOffset) = rot(i)) => (bestOffset <= i)

Termination == <>(pc = "done")

====