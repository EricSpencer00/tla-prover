---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, Printf, TLC

(* Utility library: common reusable operators for set and sequence manipulation.  This *)
(* module has no actors or system state of its own; the operators defined here are     *)
(* imported by other spec modules to implement safety and liveness properties.         *)

CONSTANTS MaxNat

\* Set intersection test: true iff sets s1 and s2 share at least one element.
INTERSECTION(s1, s2) == \E x \in s1 : x \in s2

\* Maximum (or minimum) of a non-empty set via explicit fold over its elements.
MaxOf(s) == LET f[T \in {s}](x) == IF \A y \in T : y <= x THEN x ELSE f[T \ {x}]
             IN f[s]
MinOf(s) == LET f[T \in {s}](x) == IF \A y \in T : y >= x THEN x ELSE f[T \ {x}]
             IN f[s]

\* Generalized set reduction: fold a binary operator g over a set, starting with base.
SETREDUCE(g, base, s) == LET f[T \in {s}](b) ==
                            IF T = {} THEN b
                            ELSE \E x \in T : f[T \ {x}](g(b, x))
                         IN f[s](base)

\* Sequence reduction: fold a binary operator g over a sequence, from left to right.
SEQREDUCE(g, base, seq) == LET f[i \in 1..(Len(seq) + 1)](b) ==
                              IF i > Len(seq) THEN b
                              ELSE f[i + 1](g(b, seq[i]))
                          IN f[1](base)

\* Find the index of element x in a sequence, or 0 if not present.
INDEXOF(seq, x) == LET f[i \in 1..(Len(seq) + 1)] ==
                       IF i > Len(seq) THEN 0
                       ELSE IF seq[i] = x THEN i ELSE f[i + 1]
                   IN f[1]

\* Convert sequence to the set of its elements.
SEQSET(seq) == {seq[i] : i \in 1..Len(seq)}

\* Get the last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* Test if a sequence is empty.
IsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of element x from a sequence.
REMOVEALL(seq, x) == SELECT seq[i] \in {seq[j] : j \in 1..Len(seq)} : seq[i] # x

\* Intersection of a set of sets: elements common to every member set.
SETINTERSECTION(S) == {x \in UNION S : \A Y \in S : x \in Y}

\* Generate all permutations of a finite set (as a set of sequences).
PERMUTATIONS(S) == LET f[T \in {S}](p) ==
                        IF T = {} THEN {<<>>}
                        ELSE UNION { <<x>> \o y : x \in T, y \in f[T \ {x}] }
                    IN f[S]

\* Test helper: assert cond, printing a message on failure.
TestAssert(msg, cond) == IF cond THEN TRUE
                         ELSE (PrintF("%s%n", msg); FALSE)

\* Dummy specification: a library module with no system to model.
Spec == TRUE

====