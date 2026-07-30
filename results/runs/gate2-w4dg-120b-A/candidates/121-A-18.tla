---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* The circular least-substring algorithm is modeled as a single sequential
\* process with a program counter naming each step; every identifier listed
\* in the spec (including the ones used in the reference .cfg) is exposed
\* here exactly as required.

CONSTANTS CharacterSet, Nat
None == Nat
MaxLen == 3

VARIABLES str, strLen, fail, pi, i, offset, pc
vars == <<str, strLen, fail, pi, i, offset, pc>>

\* The corpus is the set of all zero-indexed sequences over the character set
\* up to the configured maximum length.
Corpus == { s \in Seq(CharacterSet) : Len(s) <= MaxLen }

Init ==
  /\ \E s \in Corpus :
        /\ str = s
        /\ strLen = Len(s)
        /\ fail' = [j \in 0..(2 * Len(s)) |-> None]
  /\ pi' = None
  /\ i' = 1
  /\ offset' = 0
  /\ pc' = "outer"

OuterCheck ==
  /\ pc = "outer"
  /\ i < 2 * strLen
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, strLen, fail, pi, i, offset>>

Lookup ==
  /\ pc = "lookup"
  /\ fail' = [fail EXCEPT ![i - offset] = IF i - offset \in DOMAIN fail THEN fail[i - offset] ELSE None]
  /\ pi' = IF i - offset \in DOMAIN fail THEN fail[i - offset] ELSE None
  /\ pc' = "compare"
  /\ UNCHANGED <<str, strLen, i, offset>>

\* The inner loop compares characters and follows the failure chain; the
\* two branches below capture the update vs. follow-path cases.
Compare ==
  /\ pc = "compare"
  /\ LET cur == str[(i % strLen) + 1]
         cand == str[((offset + i) % strLen) + 1]
     IN
        IF cur = cand
        THEN pc' = "post"
        ELSE IF pi # None
             THEN pc' = "follow"
             ELSE pc' = "post"
  /\ UNCHANGED <<str, strLen, fail, pi, i, offset>>

Update ==
  /\ pc = "compare"
  /\ pi = None
  /\ LET cur == str[(i % strLen) + 1]
         cand == str[((offset + i) % strLen) + 1]
     IN cur < cand /\ offset' = i
  /\ UNCHANGED <<str, strLen, fail, pi, i, pc>>

Follow ==
  /\ pc = "follow"
  /\ pi # None
  /\ pi' = fail[pi]
  /\ pc' = "compare"
  /\ UNCHANGED <<str, strLen, fail, i, offset>>

Post ==
  /\ pc = "post"
  /\ LET cur == str[(i % strLen) + 1]
         cand == str[((offset + i) % strLen) + 1]
     IN
        /\ IF cur # cand /\ pi = None /\ cur < cand THEN offset' = i ELSE UNCHANGED offset
        /\ fail' = [fail EXCEPT ![i - offset] = IF pi = None THEN None ELSE pi + 1]
  /\ pi' = None
  /\ pc' = "incr"
  /\ UNCHANGED <<str, strLen, i>>

Incr ==
  /\ pc = "incr"
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, strLen, fail, pi, offset>>

Done ==
  /\ pc = "outer"
  /\ i >= 2 * strLen
  /\ pc' = "done"
  /\ UNCHANGED <<str, strLen, fail, pi, i, offset>>

Quiesce == UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ Compare \/ Update \/ Follow \/ Post \/ Incr \/ Done \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Quiesce)

TypeInvariant ==
  /\ str \in Corpus
  /\ strLen = Len(str)
  /\ fail \in [0..(2 * strLen) -> {None} \cup 0..(2 * strLen)]
  /\ pi \in {None} \cup (0..(2 * strLen))
  /\ i \in 0..(2 * strLen)
  /\ offset \in 0..(strLen - 1)

OffsetIsLexLeastRotation ==
  LET rot(k) == <<str[(k % strLen) + 1]>> @@ (IF strLen > 1 THEN SubSeq(str, ((k % strLen) + 2), strLen) ELSE <<>>)
  IN \A j \in 0..(strLen - 1) : rot(offset) <= rot(j)

Termination == <>(pc = "done")

SpecFormula == Spec
TypeInv == TypeInvariant
Correctness == OffsetIsLexLeastRotation
Terminating == Termination
====