---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  MaxSeqLen,
  MaxSetSize,
  MaxSetValue,
  MaxSeqValue

VARIABLES
  specState,
  specStep

vars == <<specState, specStep>>

TypeOK ==
  /\ specState \in {"init", "done"}
  /\ specStep \in 0 .. MaxSeqLen

Init ==
  /\ specState = "init"
  /\ specStep = 0

Step ==
  /\ specStep < MaxSeqLen
  /\ specStep' = specStep + 1
  /\ UNCHANGED specState

SpecDone ==
  /\ specState = "done"
  /\ UNCHANGED vars

Next == Step \/ SpecDone

Spec == Init /\ [][Next]_vars

TestHelper(P, msg) == msg /\ P

Overlaps(s, t) == \E x \in s : x \in t

SetMax(S) == LET M[k \in S] ==
                  IF \A y \in S : k >= y THEN k ELSE M[CHOOSE y \in S : y > k]
              IN M[CHOOSE x \in S : TRUE]

SetMin(S) == LET m[k \in S] ==
                  IF \A y \in S : k <= y THEN k ELSE m[CHOOSE y \in S : y < k]
              IN m[CHOOSE x \in S : TRUE]

SetReduce(f, S) ==
  LET Fold[T \in SUBSET S] ==
       IF T = {} THEN 0
       ELSE LET x == CHOOSE y \in T : TRUE IN f[x, Fold[T \ {x}]]
  IN Fold[S]

SeqReduce(f, s) == FoldSeq(f, s)

SeqIndex(s, x) == CHOOSE k \in DOMAIN s : s[k] = x

SeqToSet(s) == { s[k] : k \in DOMAIN s }

SeqLast(s) == s[Len(s)]

SeqEmpty(s) == Len(s) = 0

SeqRemove(s, x) ==
  LET Rec(k) ==
       IF k > Len(s) THEN << >>
       ELSE IF s[k] = x THEN Rec(k + 1) ELSE << s[k] >> ^ Rec(k + 1)
  IN Rec(1)

SetIntersectOfSets(S) ==
  LET Fold[T \in SUBSET S] ==
       IF T = {} THEN {}
       ELSE LET x == CHOOSE y \in T : TRUE IN x \cap Fold[T \ {x}]
  IN Fold[S]

SetPermutations(S) ==
  LET Rec(Seq) ==
       IF Seq = {} THEN {}
       ELSE
         UNION { LET Rest == Rec(Seq \ {e}) IN
                 IF Rest = {} THEN {<< e >>}
                 ELSE { << e >> ^ r : r \in Rest } }
  IN Rec(S)

====