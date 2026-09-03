---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Tokens

ASSUME /\ \E e \in Tokens : e > 0
       /\ Cardinality(Naturals) > 0

SetIntersection(A, B) == \E a \in A : a \in B
SetChoose(S) == CHOOSE e \in S : TRUE
SetReduce(f, S, a0) == IF S = {} THEN a0 ELSE SetReduce(f, S \ {SetChoose(S)}, f(SetChoose(S), a0))
SeqReduce(f, seq, a0) == ReduceSeq(f, seq, a0)
SeqIndexOf(seq, e) == CHOOSE i \in DOMAIN seq : seq[i] = e
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }
SeqIntersection(sets) == { e \in UNION sets : \A s \in sets : e \in s }
SeqPermutations(S) == { s \in [1..Cardinality(S) -> S] : \A i, j \in DOMAIN s : s[i] = s[j] => i = j }
SeqRemoveAll(seq, e) == SelectSeq(seq, LAMBDA x : x # e)
SeqNotEmpty(seq) == seq # << >>

\* Test helper that prints a message on failure (no effect on the model itself).
\* Unfortunately TLA+ assertions can only print the message on failure, never
\* the full bounded context, so this is intentionally simple.
Assert(expr, msg) == IF expr THEN TRUE ELSE (msg /\ FALSE)

====