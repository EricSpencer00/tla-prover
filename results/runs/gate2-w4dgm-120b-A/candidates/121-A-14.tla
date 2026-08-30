---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet

\* Zero-indexed sequences over a finite character set, with a bounded length.
Corpus == UNION { [1..n -> CharacterSet] : n \in 0..MaxLen }
MaxLen == 2
Sentinel == 9

VARIABLES input, len, fail, pIdx, loopCtr, bestOffset, pc

vars == <<input, len, fail, pIdx, loopCtr, bestOffset, pc>>

TypeInvariant ==
    /\ input \in Corpus
    /\ len = Len(input)
    /\ fail \in [0..2*MaxLen -> 0..MaxLen \cup {Sentinel}]
    /\ pIdx \in 0..MaxLen \cup {Sentinel}
    /\ loopCtr \in 1..2*MaxLen
    /\ bestOffset \in 0..MaxLen-1
    /\ pc \in {"outer", "lookup", "inner", "mismatch", "follow", "post", "done"}

Init ==
    /\ \E s \in Corpus : input = s
    /\ len = Len(input)
    /\ fail = [k \in 0..2*MaxLen |-> Sentinel]
    /\ pIdx = Sentinel
    /\ loopCtr = 1
    /\ bestOffset = 0
    /\ pc = "outer"

\* Outer loop guarding the linear scan over the doubled string.
Outer ==
    /\ pc = "outer"
    /\ IF loopCtr < 2 * len THEN pc' = "lookup" ELSE pc' = "done"
    /\ UNCHANGED <<input, len, fail, pIdx, loopCtr, bestOffset>>

\* Failure-function lookup at the current position relative to the best offset.
Lookup ==
    /\ pc = "lookup"
    /\ pIdx' = fail[loopCtr % len - bestOffset]
    /\ pc' = "inner"
    /\ UNCHANGED <<input, len, fail, loopCtr, bestOffset>>

\* Inner character comparison loop; runs while the pattern match holds.
Inner ==
    /\ pc = "inner"
    /\ IF input[loopCtr % len] # input[(loopCtr % len) - bestOffset] /\ pIdx # Sentinel
         THEN pc' = "mismatch"
         ELSE pc' = "post"
    /\ UNCHANGED <<input, len, fail, pIdx, loopCtr, bestOffset>>

\* A new lexicographic minimum was found while the pattern was still matching.
Mismatch ==
    /\ pc = "mismatch"
    /\ input[loopCtr % len] < input[(loopCtr % len) - bestOffset]
    /\ bestOffset' = loopCtr % len
    /\ pc' = "follow"
    /\ UNCHANGED <<input, len, fail, pIdx, loopCtr>>

\* Follow the failure function chain one step.
Follow ==
    /\ pc = "follow"
    /\ pIdx' = fail[pIdx]
    /\ pc' = "inner"
    /\ UNCHANGED <<input, len, fail, loopCtr, bestOffset>>

\* Post-comparison: either reset or extend the failure function.
Post ==
    /\ pc = "post"
    /\ IF input[loopCtr % len] # input[(loopCtr % len) - bestOffset] /\ pIdx = Sentinel
         THEN
           /\ IF input[loopCtr % len] < input[(loopCtr % len) - bestOffset]
                THEN bestOffset' = loopCtr % len
                ELSE bestOffset' = bestOffset
           /\ fail' = [fail EXCEPT ![loopCtr % len] = Sentinel]
         ELSE fail' = [fail EXCEPT ![loopCtr % len] = pIdx + 1]
    /\ pIdx' = Sentinel
    /\ loopCtr' = loopCtr + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<input, len>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Outer
    \/ Lookup
    \/ Inner
    \/ Mismatch
    \/ Follow
    \/ Post
    \/ Done

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Outer)
    /\ WF_vars(Lookup)
    /\ WF_vars(Inner)
    /\ WF_vars(Mismatch)
    /\ WF_vars(Follow)
    /\ WF_vars(Post)

\* A rotation is lexicographically minimal iff it is <= every other rotation,
\* and among equal rotations it has the smallest shift (offset) value.
Correctness ==
    /\ \A k \in 0..len-1 :
         \A j \in 0..len-1 :
           ( \A n \in 0..len-1 : input[(k + n) % len] <= input[(j + n) % len] )
             => ( k <= j \/ ( \E m \in 0..len-1 : input[(k + m) % len] < input[(j + m) % len] ) )
    /\ \A k \in 0..len-1 :
         ( \A n \in 0..len-1 : input[(k + n) % len] = input[(bestOffset + n) % len] )
           => k >= bestOffset

Termination == (pc # "done") ~> (pc = "done")

====