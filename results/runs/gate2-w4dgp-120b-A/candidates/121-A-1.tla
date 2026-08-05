---- MODULE LeastCircularSubstring ----
EXTENDS Integers

(* This module implements the lexicographically-least circular substring algorithm  *)
(* from Booth's 1980 paper (Information Processing Letters, doi:10.1016/0020-0190  *)
(* (80)90149-0).  The algorithm works over a nondeterministically-chosen input  *)
(* string (a sequence of characters from a finite character set) and, in linear *)
(* time, finds the rotation that yields the lexicographically smallest string.   *)
(* The failure function used here is the same as KMP's failure function.          *)

CONSTANTS CharacterSet

ASSUME
  /\ CharacterSet \subseteq Nat
  /\ CharacterSet # {}

VARIABLES inputString, length, failure, patternMatch, loopCounter, bestOffset, pc

vars == << inputString, length, failure, patternMatch, loopCounter, bestOffset, pc >>

(* The full set of zero-indexed sequences over the character set -- the corpus   *)
(* of strings this algorithm must handle.  The model-checker bounds the size     *)
(* of CharacterSet and the maximum string length so this set stays finite.       *)
Sequences == { f \in [Nat -> CharacterSet] : ( \E n \in Nat : \A k \in Nat : k > n => f[k] = 0 ) /\ ( \E n \in Nat : \A k \in Nat : k > n => f[k] = 0 ) }

Sentinel == 0 - 1

TypeInvariant ==
  /\ inputString \in Sequences
  /\ length = Cardinality({ k \in Nat : inputString[k] # 0 })
  /\ failure \in [0..(2 * length - 1) -> {Sentinel} \cup (0..(2 * length - 1))]
  /\ patternMatch \in {Sentinel} \cup (0..(2 * length - 1))
  /\ loopCounter \in 1..(2 * length)
  /\ bestOffset \in 0..(length - 1)
  /\ pc \in {sOutLoopCheck, sFailureLookup, sInnerCompare, sUpdateOffset, sFailureFollow, sPostCompare, sStall}

Init ==
  /\ \E seq \in Sequences : inputString = seq /\ length = Cardinality({ k \in Nat : seq[k] # 0 })
  /\ failure = [k \in 0..(2 * length - 1) |-> Sentinel]
  /\ patternMatch = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = sOutLoopCheck

(* Outer loop over positions up to twice the string length (covers the wrap)    *)
OutLoopCheck ==
  /\ pc = sOutLoopCheck
  /\ (loopCounter < 2 * length) /\ pc' = sFailureLookup
  \/ (loopCounter >= 2 * length) /\ pc' = sStall
  /\ UNCHANGED << inputString, length, failure, patternMatch, loopCounter, bestOffset >>

FailureLookup ==
  /\ pc = sFailureLookup
  /\ patternMatch' = failure[(bestOffset + loopCounter) % length]
  /\ pc' = sInnerCompare
  /\ UNCHANGED << inputString, length, failure, loopCounter, bestOffset >>

(* Compare the character at the current loop position with the character at the *)
(* candidate position given the current best offset.                          *)
InnerCompare ==
  /\ pc = sInnerCompare
  /\ IF (inputString[loopCounter % length] # inputString[(bestOffset + loopCounter) % length])
       /\ patternMatch # Sentinel
     THEN pc' = sFailureFollow
     ELSE pc' = sPostCompare
  /\ UNCHANGED << inputString, length, failure, patternMatch, loopCounter, bestOffset >>

(* If the current character is strictly less, the candidate rotation is better *)
(* than anything seen before, so update the best offset.                        *)
UpdateOffset ==
  /\ pc = sUpdateOffset
  /\ inputString[loopCounter % length] < inputString[(bestOffset + loopCounter) % length]
  /\ bestOffset' = (loopCounter + bestOffset) % length
  /\ pc' = sFailureFollow
  /\ UNCHANGED << inputString, length, failure, patternMatch, loopCounter >>

(* Follow the failure chain (KMP-style) to the next candidate match.          *)
FailureFollow ==
  /\ pc = sFailureFollow
  /\ patternMatch' = failure[patternMatch]
  /\ pc' = sInnerCompare
  /\ UNCHANGED << inputString, length, failure, loopCounter, bestOffset >>

(* If the characters still differ at the end of the chain, reset or extend the *)
(* failure function appropriately.                                             *)
PostCompare ==
  /\ pc = sPostCompare
  /\ IF (inputString[loopCounter % length] # inputString[(bestOffset + loopCounter) % length])
        /\ patternMatch = Sentinel
     THEN \/ failure' = [failure EXCEPT ![(bestOffset + loopCounter) % length] = Sentinel]
             \/ failure' = [failure EXCEPT ![(bestOffset + loopCounter) % length] = patternMatch + 1]
          /\ pc' = sUpdateOffset
     ELSE pc' = sStall /\ UNCHANGED failure
  /\ UNCHANGED << inputString, length, patternMatch, loopCounter, bestOffset >>

(* Increment the loop and return to the outer-loop check.                      *)
Stall ==
  /\ pc = sStall
  /\ pc' = sOutLoopCheck
  /\ loopCounter' = IF loopCounter < 2 * length THEN loopCounter + 1 ELSE loopCounter
  /\ UNCHANGED << inputString, length, failure, patternMatch, bestOffset >>

Next == OutLoopCheck \/ FailureLookup \/ InnerCompare \/ UpdateOffset \/ FailureFollow \/ PostCompare \/ Stall

Spec == Init /\ [][Next]_vars

(* Upon termination, the recorded best offset must name the lexicographically   *)
(* minimal rotation: no other rotation yields a strictly smaller sequence, and   *)
(* among equal sequences it has the smallest shift.                             *)
Correctness ==
  /\ (loopCounter = 2 * length) => (~ \E j \in 1..(length - 1) :
        LET seq(k) == inputString[(k + bestOffset) % length]
            seqj(k) == inputString[(k + j) % length]
        IN \A k \in 0..(length - 1) : seq(k) <= seqj(k)
           /\ ( (\A k \in 0..(length - 1) : seq(k) = seqj(k)) => j >= bestOffset ))
  /\ (loopCounter < 2 * length) => TRUE

Termination == <>(loopCounter = 2 * length)

====