---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

(* ZSequences is the zero-indexed-sequence variant of the standard library's
   Seq module. *)
CONSTANTS CharacterSet

(* In the original spec this is a simple literal substitution from ZSequences to
   Naturals.  Keeping the EXTENDS Nat keeping the name out of this module's own
   namespace is what makes that legal. *)
CharacterSet == Nat

\* Sequence over the character set (zero-indexed by definition of ZSequences).
Seq == CHOOSE s \in [0..] -> CharacterSet : TRUE

Corpus == {s \in [0..] -> CharacterSet : \E n \in Nat : s \in [0..n -> CharacterSet]}
Sentinel == 100

VARIABLES seq, seqLen, failure, pattern, loopPos, bestOffset, pc

vars == <<seq, seqLen, failure, pattern, loopPos, bestOffset, pc>>

TypeInvariant ==
    /\ seq \in Corpus
    /\ seqLen = Len(seq)
    /\ failure \in [0..2 * seqLen -> 0..(seqLen \cup {Sentinel})]
    /\ pattern \in 0..(seqLen \cup {Sentinel})
    /\ loopPos \in 0..(2 * seqLen)
    /\ bestOffset \in 0..(seqLen - 1)
    /\ pc \in {"outerCheck", "lookup", "compare", "updateBest", "followChain",
               "postCompare", "increment", "done"}

Init ==
    /\ \E s \in Corpus :
         /\ seq = s
         /\ seqLen = Len(s)
    /\ failure = [i \in 0..(2 * seqLen) |-> Sentinel]
    /\ pattern = Sentinel
    /\ loopPos = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopPos < 2 * seqLen
         THEN pc' = "lookup"
         ELSE pc' = "done"
    /\ UNCHANGED <<seq, seqLen, failure, pattern, loopPos, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ failure' = [failure EXCEPT ![loopPos] = failure[bestOffset]]
    /\ pc' = "compare"
    /\ UNCHANGED <<seq, seqLen pattern, loopPos, bestOffset>>

\* The candidate position is the loop index shifted back by the current best
\* rotation.  The modulo re-wraps the index around the circular string.
Compare ==
    /\ pc = "compare"
    /\ seq[loopPos % seqLen] # seq[(loopPos - bestOffset) % seqLen]
    /\ pattern # Sentinel
    /\ pc' = "compare"
    /\ UNCHANGED <<seq, seqLen, failure, pattern, loopPos, bestOffset>>

UpdateBest ==
    /\ pc = "compare"
    /\ seq[loopPos % seqLen] < seq[(loopPos - bestOffset) % seqLen]
    /\ bestOffset' = loopPos % seqLen
    /\ pc' = "followChain"
    /\ UNCHANGED <<seq, seqLen, failure, pattern, loopPos>>

FollowChain ==
    /\ pc = "followChain"
    /\ pattern' = failure[pattern]
    /\ pc' = "postCompare"
    /\ UNCHANGED <<seq, seqLen, failure, loopPos, bestOffset>>

PostCompare ==
    /\ pc = "postCompare"
    /\ IF seq[loopPos % seqLen] # seq[(loopPos - bestOffset) % seqLen]
         THEN pc' = IF pattern = Sentinel THEN "updateBest" ELSE "postCompare"
         ELSE pc' = "increment"
    /\ failure' = IF seq[loopPos % seqLen] # seq[(loopPos - bestOffset) % seqLen]
                     THEN [failure EXCEPT ![loopPos] = IF pattern = Sentinel
                                                        THEN Sentinel
                                                        ELSE pattern + 1]
                     ELSE failure
    /\ UNCHANGED <<seq, seqLen, pattern, loopPos, bestOffset>>

Increment ==
    /\ pc = "postCompare"
    /\ loopPos' = loopPos + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<seq, seqLen, failure, pattern, bestOffset>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ Compare
    \/ UpdateBest
    \/ FollowChain
    \/ PostCompare
    \/ Increment
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

\* Lexicographic minimality of the rotation at bestOffset, and minimal shift if
\* the suffixes are equal.
Correctness ==
    /\ \A i \in 0..(seqLen - 1) :
         LET a == seq[(bestOffset + i) % seqLen]
             b == seq[i]
         IN a <= b
    /\ \A i \in 0..(seqLen - 1) :
         (seq[(bestOffset + i) % seqLen] = seq[i])
           => bestOffset <= i

Termination == <>(pc = "done")

====