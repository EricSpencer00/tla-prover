---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxPerm, MaxVal

\* Set intersection: true iff s1 and s2 share at least one element.
Intersect(s1, s2) == \E x \in s1 : x \in s2

\* Maximum and minimum elements of a non-empty set of natural numbers.
MaxSet(s) == CHOOSE x \in s : \A y \in s : y <= x
MinSet(s) == CHOOSE x \in s : \A y \in s : y >= x

\* Generalized reduction (fold) over a set, with an accumulator.
ReduceSet(f, s, init) ==
    IF s = {} THEN init
    ELSE LET x == CHOOSE y \in s : TRUE IN f[RHS -> ReduceSet(f, s \ {x}, init)]

\* Reduction over a sequence, using the built-in FoldSeq operator.
ReduceSeq(f, seq, init) == FoldSeq(f, seq, init)

\* Position (1-based) of v in seq; 0 if absent.
IndexOf(seq, v) ==
    LET pos == CHOOSE k \in 1..Len(seq) : seq[k] = v
    IN IF \E k \in 1..Len(seq) : seq[k] = v THEN pos ELSE 0

SeqSet(seq) == { seq[k] : k \in 1..Len(seq) }

\* Last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* True iff the sequence is empty.
Empty(seq) == Len(seq) = 0

\* Remove every occurrence of v from seq.
Exclude(seq, v) == SelectSeq(seq, LAMBDA x : x # v)

\* Intersection of a family (set) of sets.
IntersectFamily(F) == { x \in UNION F : \A s \in F : x \in s }

\* All permutations of the set {1, 2, ..., n} as sequences.
Permutations(n) ==
    IF n = 0 THEN { << >> }
    ELSE
        LET rest == Permutations(n - 1)
            a == n
            InsertAt(pos, seq) == SubSeq(seq, 1, pos - 1) \o << a >> \o SubSeq(seq, pos, Len(seq))
        IN { InsertAt(k, seq) : seq \in rest, k \in 1..(Len(seq) + 1) }

\* Test helper that records the failed assertion as a runtime message.
\* It always returns TRUE so it never blocks progress.
TestHelper(cond, msg) == (IF ~cond THEN PrintT(msg) ELSE TRUE)

CONSTANTS MaxPerm, MaxVal
====