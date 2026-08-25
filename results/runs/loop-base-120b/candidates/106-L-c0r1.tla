---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(* 1. Set intersection test (whether two sets overlap) *)
Overlaps(S, T) == (S \cap T) # {}

(* 2. Maximum and minimum element selection from a set *)
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold over a set with an accumulator) *)
SetReduce(S, acc, f) ==
    IF S = {} THEN acc
    ELSE
        LET e == CHOOSE x \in S : TRUE
        IN SetReduce(S \ {e}, f(acc, e), f)

(* 4. Sequence reduction (fold over a sequence with an accumulator) *)
SeqReduce(seq, acc, f) == FoldSeq(f, acc, seq)

(* 5. Finding the index of an element in a sequence *)
IndexOf(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

(* 6. Converting a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Getting the last element of a sequence *)
Last(seq) ==
    IF Len(seq) = 0 THEN NULL
    ELSE seq[Len(seq)]

(* 8. Testing if a sequence is empty *)
IsEmpty(seq) == Len(seq) = 0

(* 9. Removing all occurrences of an element from a sequence *)
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF seq[1] = elem
         THEN RemoveAll(SubSeq(seq, 2, Len(seq)), elem)
         ELSE <<seq[1]>> \o RemoveAll(SubSeq(seq, 2, Len(seq)), elem)

(* 10. Computing the intersection of a set of sets *)
SetIntersection(SS) == INTERSECTION SS

(* 11. Generating all permutation sequences of a finite set *)
PermutationsOf(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in PermutationsOf(S \ {e}) }

(* 12. Test helper for writing assertions that print diagnostic information on failure *)
TestHelper(expr, msg) ==
    IF expr THEN TRUE ELSE (Print(msg); FALSE)

(* Specification skeleton required by the task *)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====