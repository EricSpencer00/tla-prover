---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CharacterSet

\* The reference configuration replaces Naturals' Nat with a finite version of it.
\* We EXTEND Naturals so everything built on Nat still works, but we never
\* mention Nat again -- only the replacement operator below.
\* NOTE: [ZSequences]CharacterSet is the operator name, not a constant name.
ZSequencesCharacterSet == CharacterSet

VARIABLES seq, n, fail, pmi, outer, best, pc

vars == <<seq, n, fail, pmi, outer, best, pc>>

Undefined == -1
MaxLen == 3
MaxChar == 2

\* seq is a zero-indexed sequence of characters from the corpus.
\* The corpus is everything possible over the configured alphabet, up to
\* MaxLen. n is the length; fail is the KMP-like failure function array.
Init ==
  /\ \E s \in Seq(CharacterSet) :
       /\ Len(s) <= MaxLen
       /\ s # << >>
       /\ seq' = s
       /\ n' = Len(s)
  /\ fail' = [i \in 0..(2*MaxLen) |-> Undefined]
  /\ pmi' = Undefined
  /\ outer' = 1
  /\ best' = 0
  /\ pc' = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF outer < 2 * n
       THEN pc' = "lookup"
       ELSE pc' = "halt"
  /\ UNCHANGED <<seq, n, fail, pmi, outer, best>>

Lookup ==
  /\ pc = "lookup"
  /\ pmi' = fail[best + outer]
  /\ pc' = "compare"
  /\ UNCHANGED <<seq, n, fail, outer, best>>

CompareStep ==
  /\ pc = "compare"
  /\ LET cur == seq[(outer % n) + 1]
         cand == seq[((best + outer) % n) + 1]
     IN IF cur # cand /\ pmi # Undefined
           THEN pc' = "compare"
           ELSE pc' = "post"
  /\ UNCHANGED <<seq, n, fail, pmi, outer, best>>

UpdateBestLess ==
  /\ pc = "compare"
  /\ LET cur == seq[(outer % n) + 1]
         cand == seq[((best + outer) % n) + 1]
     IN cur < cand
  /\ best' = outer
  /\ UNCHANGED <<seq, n, fail, pmi, outer, pc>>

FollowFail ==
  /\ pc = "compare"
  /\ pmi # Undefined
  /\ pmi' = fail[pmi]
  /\ UNCHANGED <<seq, n, fail, outer, best, pc>>

PostCompare ==
  /\ pc = "post"
  /\ LET cur == seq[(outer % n) + 1]
         cand == seq[((best + outer) % n) + 1]
         reset == IF cur # cand /\ pmi = Undefined /\ cur < cand
                   THEN outer
                   ELSE Undefined
         ext == IF cur = cand
                  THEN IF pmi = Undefined THEN Undefined ELSE pmi + 1
                  ELSE Undefined
     IN /\ fail' = [fail EXCEPT ![best + outer] = reset]
        /\ best' = IF reset # Undefined THEN reset ELSE best
        /\ pmi' = ext
  /\ pc' = "increment"
  /\ UNCHANGED <<seq, n, outer>>

Increment ==
  /\ pc = "increment"
  /\ outer' = outer + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<seq, n, fail, pmi, best>>

Stall ==
  /\ pc = "halt"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop
  \/ Lookup
  \/ CompareStep
  \/ UpdateBestLess
  \/ FollowFail
  \/ PostCompare
  \/ Increment
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment) /\ WF_vars(Lookup)

\* The input is always a corpus sequence, n really is its length, fail is
\* a valid failure array, and all the loop indices stay inside their ranges.
TypeInvariant ==
  /\ seq \in Seq(CharacterSet)
  /\ n = Len(seq)
  /\ fail \in [0..(2 * MaxLen) -> ({Undefined} \cup (1..MaxLen))]
  /\ pmi \in {Undefined} \cup (1..MaxLen)
  /\ outer \in 1..(2 * MaxLen)
  /\ best \in 0..(n - 1)

\* The rotation starting at best is lexicographically <= every rotation
\* of seq, and among identical rotations it carries the smallest shift.
Correctness ==
  /\ \A k \in 0..(n - 1) : seq[(best % n) + 1] <= seq[(k % n) + 1]
  /\ \A k \in 0..(n - 1) :
       seq[(best % n) + 1] = seq[(k % n) + 1] => best <= k

Termination == <>(pc = "halt")

====