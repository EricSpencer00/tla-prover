---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Utility operators used by the key-value store specifications.
   No state variables, actions, or properties are defined because this
   module is purely functional.  The identifiers required by the .cfg
   file (SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES) are
   defined as trivial stubs so that the configuration can reference them.
   ---------------------------------------------------------------------- *)

\* 1) Set intersection test – returns TRUE iff the two sets overlap.
Intersect?(A, B) == A \cap B # {}

\* 2) Maximum element of a non‑empty finite set.
Max(S) == 
   IF S = {} THEN 0
   ELSE LET m == CHOOSE x \in S : \A y \in S : y <= x IN m

\* 2) Minimum element of a non‑empty finite set.
Min(S) == 
   IF S = {} THEN 0
   ELSE LET m == CHOOSE x \in S : \A y \in S : x <= y IN m

\* 3) Generalized set reduction (fold over a set with an accumulator).
SetFold(Fun, Acc, S) == 
   IF S = {} THEN Acc
   ELSE 
     LET x == CHOOSE y \in S : TRUE IN
     SetFold(Fun, Fun(Acc, x), S \ {x})

\* 4) Sequence reduction (fold over a sequence with an accumulator).
SeqFold(Fun, Acc, <<>>) == Acc
SeqFold(Fun, Acc, <<x>> \o rest) == SeqFold(Fun, Fun(Acc, x), rest)

\* 5) Find the index (1‑based) of element e in sequence s; returns 0 if not found.
IndexOf(e, s) == 
   IF e \notin s THEN 0
   ELSE 
     \E i \in 1..Len(s) : 
        /\ s[i] = e
        /\ \A j \in 1..(i-1) : s[j] # e
        /\ i

\* 6) Convert a sequence to the set of its elements.
Seq2Set(s) == { s[i] : i \in 1..Len(s) }

\* 7) Get the last element of a non‑empty sequence.
Last(s) == s[Len(s)]

\* 8) Test if a sequence is empty.
SeqIsEmpty(s) == Len(s) = 0

\* 9) Remove all occurrences of element e from sequence s.
SeqFilter(s, e) == 
   [i \in 1..(Len(s) - Cardinality({ j \in 1..Len(s) : s[j] = e })) |-> 
        s[ 
            IF i < (Min({ j \in 1..Len(s) : s[j] = e } \cup {Len(s)+1})) THEN i
            ELSE i + Cardinality({ j \in 1..Len(s) : s[j] = e /\ j <= i })
        ]]

\* 10) Intersection of a non‑empty set of sets.
SetIntersection(S) == 
   IF S = {} THEN {}
   ELSE /\ \A X \in S : X \subseteq UNION S
        /\ \A e \in UNION S : (\A X \in S : e \in X) => e \in SetIntersection(S)

\* 11) Generate all permutations of a finite set.
Permutations(S) == 
   IF S = {} THEN { <<>> }
   ELSE { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* 12) Test helper that prints a message when the condition fails.
Assert(cond, msg) == 
   IF cond THEN TRUE 
   ELSE 
     PrintT("Assertion failed: ", msg);
     FALSE

\* ----------------------------------------------------------------------
   Trivial identifiers required by the reference .cfg.
   They do not affect the functional part of this library.
   ---------------------------------------------------------------------- *)

SPECIFICATION == 
   /\ TRUE

INIT == 
   /\ TRUE

NEXT == 
   /\ UNCHANGED {}

INVARIANTS == 
   {}

PROPERTIES == 
   {}

=============================================================================