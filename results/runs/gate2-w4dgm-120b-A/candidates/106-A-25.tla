---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(* Utility functions shared by the key-value store specs.  This module has  *)
(* no actors of its own; it merely collects reusable set and sequence ops.  *)

CONSTANTS NONE

\* 1. set intersection: TRUE iff the two sets share at least one element.
Intersecting(s, t) == \E x \in s : x \in t

\* 2. selector: the maximum element of a non-empty set (by Naturals order).
SetMax(s) == CHOOSE x \in s : \A y \in s : y <= x

\*    selector: the minimum element of a non-empty set.
SetMin(s) == CHOOSE x \in s : \A y \in s : x <= y

\* 3. generalized set reduction (fold): compute an aggregated value from a set
\*    by repeatedly applying the binary operator to an element and the running
\*    accumulator.  Since Sets are unordered the order of folding is arbitrary.
SetFold(op, s, init) ==
  LET Rec(T, a) ==
        IF T = {} THEN a
        ELSE LET e == CHOOSE x \in T : TRUE
             IN Rec(T \ {e}, op[e, a])
  IN Rec(s, init)

\* 4. sequence reduction (fold): aggregate a sequence from left to right.
SeqFold(op, seq, init) == FoldL(seq, op, init)

\* 5. index of element e in sequence seq (or Len(seq)+1 if absent).
SeqIndex(seq, e) == CHOOSE i \in 1..Len(seq) : seq[i] = e

\* 6. the set of elements occurring in a sequence.
SeqSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. the last element of a non-empty sequence (or NONE when empty).
SeqLast(seq) == IF seq = <<>> THEN NONE ELSE seq[Len(seq)]

\* 8. test whether a sequence is empty.
SeqIsEmpty(seq) == seq = <<>>

\* 9. remove all occurrences of element e from sequence seq.
SeqRemove(seq, e) == SelectSeq(seq, LAMBDA x : x # e)

\* 10. intersection of a set of sets: the elements common to every member set.
SetIntersectionOf(S) ==
  { x \in UNION S : \A t \in S : x \in t }

\* 11. generate all permutation sequences of a finite set s.
Permutations(s) ==
  { p \in [1..Cardinality(s) -> s] :
        \A i, j \in 1..Cardinality(s) : (p[i] = p[j]) => (i = j) }

\* 12. test helper: prints `msg` and aborts the spec when the condition fails.
Test(msg, cond) == IF cond THEN TRUE ELSE (Print(msg); FALSE)

(* The module itself carries no system behavior, so the spec is a trivial *)
(* tautology that always holds; its purpose is solely to expose the ops. *)
Spec == TRUE
====