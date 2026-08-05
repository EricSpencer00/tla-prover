---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS

ASSUME
  \A c \in CONSTANTS : TRUE

INTERSECTING(A, B) == \E x \in A : x \in B

MaxOf(S) ==
  LET g[f \in [S -> BOOLEAN], x \in S] ==
        IF \A y \in S : f[y] => y <= x THEN x
        ELSE g[f, x - 1]
  IN g[([x \in S |-> TRUE]), 1]

MinOf(S) ==
  LET g[f \in [S -> BOOLEAN], x \in S] ==
        IF \A y \in S : f[y] => y >= x THEN x
        ELSE g[f, x + 1]
  IN g[([x \in S |-> TRUE]), 1]

SetReduc(S, v, f) ==
  IF S = {} THEN v
  ELSE LET x == MaxOf(S) IN f[SetReduc(S \ {x}, v, f), x]

SeqReduc(seq, v, f) ==
  [x \in 1 .. Len(seq) |-> IF x = 1 THEN f[v, seq[1]] ELSE f[SeqReduc(seq, v, f)[x - 1], seq[x]]]

SeqIndex(seq, n) ==
  LET g[x \in 0 .. Len(seq)] == IF x = 0 THEN n ELSE IF seq[x] = n THEN x ELSE g[x - 1]
  IN g[Len(seq)]

SeqToSet(seq) ==
  {seq[i] : i \in 1 .. Len(seq)}

Permutations(s) ==
  LET f[S \in SUBSET s] ==
        IF S = {} THEN <<>>
        ELSE {<<x>> \o p : x \in S, p \in f[S \ {x}]}
  IN f[s]

Last(seq) ==
  seq[Len(seq)]

EmptySeq == <<>>

RemoveFromSeq(seq, n) ==
  {seq[i] : i \in 1 .. Len(seq) : seq[i] # n}

SetIntersection(S) ==
  {x \in UNION S : \A U \in S : x \in U}

TestHelper(p, msg) == IF p THEN TRUE ELSE (msg; FALSE)

====