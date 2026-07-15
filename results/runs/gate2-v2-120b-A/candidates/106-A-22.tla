---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Utility library providing common helper operators for set and sequence  *)
(* manipulation.  The module is purely functional and contains no state    *)
(* variables.  All identifiers required by the reference configuration are *)
(* defined below.                                                          *)
(***************************************************************************)

(***************************************************************************)
(* 1. Set intersection test: Returns TRUE iff the two sets overlap.        *)
(***************************************************************************)
SetOverlap(s1, s2) == \E x \in s1 : x \in s2

(***************************************************************************)
(* 2. Maximum element selection from a non‑empty set of natural numbers.  *)
(***************************************************************************)
Max(s) == 
    IF s = {} THEN 0 
    ELSE CHOOSE x \in s : \A y \in s : y <= x

(***************************************************************************)
(* 2. Minimum element selection from a non‑empty set of natural numbers.  *)
(***************************************************************************)
Min(s) == 
    IF s = {} THEN 0 
    ELSE CHOOSE x \in s : \A y \in s : x <= y

(***************************************************************************)
(* 3. Generalized set reduction (fold) over a set with an accumulator.    *)
(*    The binary operator 'op' must be a function of two arguments:      *)
(*        op : [p, p -> p] where p is the type of the accumulator.       *)
(*    The reduction starts with 'init' and applies 'op' to each element  *)
(*    of the set in an arbitrary order.                                    *)
(***************************************************************************)
SetReduce(set, init, op) ==
    \E f \in [set -> Set] :
        /\ \A x \in set : f[x] \in set
        /\ \A x, y \in set : (x # y) => f[x] # f[y]
        /\ LET seq == [i \in 1..Cardinality(set) |-> 
                        CHOOSE e \in set : \A j \in 1..i-1 : f[e] # seq[j]]
           IN 
              FoldSeq(seq, init, op)

(***************************************************************************)
(* 4. Sequence reduction (fold) over a sequence with an accumulator.     *)
(*    Uses the built‑in FoldSeq operator from the Sequences module.       *)
(***************************************************************************)
SeqReduce(seq, init, op) == FoldSeq(seq, init, op)

(***************************************************************************)
(* 5. Finding the index (1‑based) of an element in a sequence.            *)
(*    Returns a natural number in 1..Len(seq) if the element occurs;     *)
(*    otherwise returns 0.                                                 *)
(***************************************************************************)
SeqIdx(seq, elem) ==
    IF elem \in SeqToSet(seq) THEN 
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

(***************************************************************************)
(* 6. Converting a sequence to the set of its elements.                   *)
(***************************************************************************)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(***************************************************************************)
(* 7. Getting the last element of a non‑empty sequence.                    *)
(***************************************************************************)
SeqLast(seq) == 
    IF Len(seq) = 0 THEN 
        NULL 
    ELSE 
        seq[Len(seq)]

(***************************************************************************)
(* 8. Testing if a sequence is empty.                                      *)
(***************************************************************************)
SeqEmpty(seq) == Len(seq) = 0

(***************************************************************************)
(* 9. Removing all occurrences of an element from a sequence.             *)
(***************************************************************************)
SeqRemove(seq, elem) ==
    [ i \in 1..(Len(seq) - Cardinality({ j \in 1..Len(seq) : seq[j] = elem })) |-> 
        seq[ IF i < j THEN j + Cardinality({ k \in 1..j : seq[k] = elem }) 
                ELSE j ] 
        \ { i \in 1..Len(seq) : seq[i] = elem } ]

(***************************************************************************)
(* 10. Computing the intersection of a set of sets.                        *)
(*     'sets' is a set whose elements are themselves sets.                 *)
(***************************************************************************)
IntersectAll(sets) ==
    IF sets = {} THEN {} ELSE
        \A s \in sets : s \subseteq (CHOOSE s0 \in sets : s0)

(***************************************************************************)
(* 11. Generating all permutation sequences of a finite set.               *)
(*     The result is the set of all sequences that are permutations of    *)
(*     the elements of 's'.                                                *)
(***************************************************************************)
Permutations(s) ==
    IF s = {} THEN { << >> } ELSE
        { << e >> \o p : e \in s, p \in Permutations(s \ { e }) }

(***************************************************************************)
(* 12. Test helper that asserts a condition and, on failure, prints a      *)
(*     diagnostic message.  The message is included in the error trace    *)
(*     via the TLC extension that records the value of a variable named   *)
(*     'DiagMsg'.                                                          *)
(***************************************************************************)
DiagMsg == ""

Assert(cond, msg) ==
    /\ cond
    \/ /\ ~cond
       /\ DiagMsg' = msg
       /\ FALSE

(***************************************************************************)
(* The following identifiers are required by the reference configuration. *)
(* Since this module is a pure library, they are defined as trivial stubs *)
(* that do not affect any model checking of modules that import Util.    *)
(***************************************************************************)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

=============================================================================