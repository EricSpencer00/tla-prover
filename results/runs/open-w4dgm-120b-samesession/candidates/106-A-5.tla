---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS ATOM

SetOverlap(S, T) == S \cap T # {}
SetMax(S) == CHOOSE m \in S : \A x \in S : x <= m
SetMin(S) == CHOOSE m \in S : \A x \in S : m <= x
SetFold(f, S, a) == IF S = {} THEN a
                    ELSE LET x == CHOOSE y \in S : TRUE
                         IN SetFold(f, S \ {x}, f[a, x])
SeqFold(f, s, a) == FoldSeq(f, s, a)
SeqFind(s, x) == CHOOSE i \in DOMAIN s : s[i] = x
SeqToSet(s) == { s[i] : i \in DOMAIN s }
SeqLast(s) == s[Len(s)]
SeqEmpty(s) == Len(s) = 0
SeqRemoveAll(s, x) == SelectSeq(s, LAMBDA y : y # x)
SetSeqIntersection(F) ==
  IF F = {}
  THEN {}
  ELSE LET h == CHOOSE t \in F : TRUE
           k == SetSeqIntersection(F \ {h})
       IN h \cap k
AllPermutations(S) ==
  IF S = {}
  THEN { << >> }
  ELSE UNION { [x] \o p : x \in S, p \in AllPermutations(S \ {x}) }

TestHelper(p, msg) == IF p THEN "pass" ELSE msg

====