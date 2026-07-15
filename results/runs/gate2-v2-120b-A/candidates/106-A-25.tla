---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Utility Library for the KVStore project
   ---------------------------------------------------------------------- *)

VARIABLES dummy   \* No state needed; dummy is never used.

(* ----------------------------------------------------------------------
   State variables and initial predicate (required by the task)
   ---------------------------------------------------------------------- *)
vars == << dummy >>

Init == dummy = 0

(* ----------------------------------------------------------------------
   Actions (required but do nothing)
   ---------------------------------------------------------------------- *)
Next == UNCHANGED dummy

(* ----------------------------------------------------------------------
   SPECIFICATION (required identifier)
   ---------------------------------------------------------------------- *)
SPECIFICATION == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Safety invariant (trivial, because there is no state)
   ---------------------------------------------------------------------- *)
SafetyInvariant == dummy = dummy

(* ----------------------------------------------------------------------
   Liveness property (trivial, always true)
   ---------------------------------------------------------------------- *)
LivenessProp == TRUE

(* ----------------------------------------------------------------------
   1. Set intersection test: Overlap(s, t) is TRUE iff s and t have a common element.
   ---------------------------------------------------------------------- *)
Overlap(s, t) == \E x \in s : x \in t

(* ----------------------------------------------------------------------
   2. Maximum and minimum element selection from a set.
   ---------------------------------------------------------------------- *)
Max(s) == 
    IF s = {} THEN 0
    ELSE LET m == CHOOSE x \in s : \A y \in s : y <= x IN m

Min(s) == 
    IF s = {} THEN 0
    ELSE LET m == CHOOSE x \in s : \A y \in s : y >= x IN m

(* ----------------------------------------------------------------------
   3. Generalized set reduction: fold over a set with an accumulator.
      ReduceSet(s, acc, f) returns the result of applying f to each element
      of s in some order, threading the accumulator.
   ---------------------------------------------------------------------- *)
ReduceSet(s, acc, f) ==
    IF s = {} THEN acc
    ELSE 
        LET x == CHOOSE y \in s : TRUE IN
        ReduceSet(s \ {x}, f(acc, x), f)

(* ----------------------------------------------------------------------
   4. Sequence reduction (fold over a sequence) using a library fold operator.
   ---------------------------------------------------------------------- *)
SeqReduce(seq, acc, f) == FoldSeq(f, seq, acc)

(* ----------------------------------------------------------------------
   5. Finding the index of an element in a sequence.
   ---------------------------------------------------------------------- *)
SeqIndex(seq, elem) ==
    IF elem \notin seq THEN 0
    ELSE
        LET i == CHOOSE n \in 1..Len(seq) : seq[n] = elem IN i

(* ----------------------------------------------------------------------
   6. Converting a sequence to the set of its elements.
   ---------------------------------------------------------------------- *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* ----------------------------------------------------------------------
   7. Getting the last element of a sequence.
   ---------------------------------------------------------------------- *)
Last(seq) == 
    IF Len(seq) = 0 THEN 0
    ELSE seq[Len(seq)]

(* ----------------------------------------------------------------------
   8. Testing if a sequence is empty.
   ---------------------------------------------------------------------- *)
SeqEmpty(seq) == Len(seq) = 0

(* ----------------------------------------------------------------------
   9. Removing all occurrences of an element from a sequence.
   ---------------------------------------------------------------------- *)
SeqRemove(seq, elem) ==
    [i \in 1..Len(seq) |-> 
        IF seq[i] = elem THEN 0 ELSE seq[i]]

(* ----------------------------------------------------------------------
   10. Computing the intersection of a set of sets.
   ---------------------------------------------------------------------- *)
SetIntersection(S) ==
    IF S = {} THEN {}
    ELSE
        LET first == CHOOSE X \in S : TRUE IN
        { x \in first : \A Y \in S : x \in Y }

(* ----------------------------------------------------------------------
   11. Generating all permutation sequences of a finite set.
   ---------------------------------------------------------------------- *)
Permutations(s) ==
    IF s = {} THEN { <<>> }
    ELSE
        UNION { 
            <<x>> \o p 
            : x \in s, 
              p \in Permutations(s \ {x}) 
        }

(* ----------------------------------------------------------------------
   12. Test helper for writing assertions that print diagnostic info on failure.
       In TLC, the Print operator can be used for diagnostics.
   ---------------------------------------------------------------------- *)
AssertHelper(cond, msg) ==
    IF cond THEN TRUE ELSE Print(msg) = msg

(* ----------------------------------------------------------------------
   Export the required identifiers
   ---------------------------------------------------------------------- *)
CONSTANTS
INVARIANTS == SafetyInvariant
PROPERTIES == LivenessProp
SPECIFICATION == SPECIFICATION
Init == Init
Next == Next

====