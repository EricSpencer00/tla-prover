---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Zero-indexed sequence utility: the model checker only ever sees
\* SubSeq, Len, and SelectSeq, so the full set of ZSequences operators
\* is not needed here -- Len and SelectSeq are the ones we use.
Seq == STRING

Indices == 0..(Len(Seq) - 1)

VARIABLES str, n, fail, patternIdx, outer, best, pc

vars == <<str, n, fail, patternIdx, outer, best, pc>>

\* The sentinel marking "undefined" for the failure function entries.
Sentinel == n

TypeInvariant ==
    /\ str \in Seq
    /\ n \in Nat
    /\ fail \in [0..(2 * n) -> 0..(n + 1)]
    /\ patternIdx \in 0..(n + 1)
    /\ outer \in 0..(2 * n)
    /\ best \in 0..(n - 1)
    /\ pc \in {OuterCheck, Lookup, InnerLoop, FollowChain, PostCompare, Stutter}

\* Whether the circular substring at offset o is lexicographically
\* minimal among all rotations of str, with a strict tie-breaker on o.
IsMinimal(o) ==
    /\ \A i \in 0..(n - 1) : \A k \in 0..(n - 1) :
         IF \A j \in 0..(n - 1) : str[(i + j) % n] = str[(k + j) % n]
         THEN k >= i
         ELSE \E j \in 0..(n - 1) : str[(i + j) % n] < str[(k + j) % n]
    /\ o = n \/ \A k \in 0..(n - 1) : str[(o + k) % n] = str[(k) % n]

Init ==
    /\ \E s \in Seq :
         /\ s \in [Indices -> CharacterSet]
         /\ str' = s
    /\ n' = Len(str)
    /\ fail' = [i \in 0..(2 * n) |-> Sentinel]
    /\ patternIdx' = Sentinel
    /\ outer' = 1
    /\ best' = 0
    /\ pc' = OuterCheck

OuterCheck ==
    /\ pc = OuterCheck
    /\ outer < 2 * n
    /\ pc' = Lookup
    /\ UNCHANGED <<str, n, fail, patternIdx, outer, best>>

Lookup ==
    /\ pc = Lookup
    /\ fail' = [fail EXCEPT ![outer - best] = patternIdx]
    /\ pc' = InnerLoop
    /\ UNCHANGED <<str, n, patternIdx, outer, best>>

\* Direct comparison of the candidate rotation against the best so far.
InnerLoop ==
    /\ pc = InnerLoop
    /\ str[outer % n] # str[(outer - best) % n]
    /\ patternIdx # Sentinel
    /\ patternIdx' = fail[outer - best]
    /\ pc' = FollowChain
    /\ UNCHANGED <<str, n, fail, outer, best>>

FollowChain ==
    /\ pc = FollowChain
    /\ patternIdx # Sentinel
    /\ patternIdx' = fail[outer - best]
    /\ pc' = PostCompare
    /\ UNCHANGED <<str, n, fail, outer, best>>

PostCompare ==
    /\ pc = PostCompare
    /\ IF str[outer % n] < str[(outer - best) % n]
         THEN best' = outer
         ELSE best' = best
    /\ fail' = IF patternIdx = Sentinel
               THEN [fail EXCEPT ![outer - best] = Sentinel]
               ELSE [fail EXCEPT ![outer - best] = patternIdx + 1]
    /\ patternIdx' = IF patternIdx = Sentinel THEN Sentinel ELSE patternIdx + 1
    /\ outer' = outer + 1
    /\ pc' = OuterCheck

Stutter ==
    /\ pc = Stutter
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ FollowChain
    \/ PostCompare
    \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Stutter)

Termination ==
    (pc # OuterCheck) ~> (pc = OuterCheck)

Correctness == IsMinimal(best)

====