---- MODULE Quicksort
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* If you are not already familiar with that algorithm, you should look it *)
(* up on the Web and understand how it works--including what the partition *)
(* procedure does, without worrying about how it does it.  The version     *)
(* presented here does not specify a partition procedure, but chooses in a *)
(* single step an arbitrary value that is the result that any partition    *)
(* procedure may produce.                                                  *)
(*                                                                         *)
(* The module also has a structured informal proof of Quicksort's partial  *)
(* correctness property--namely, that if it terminates, it produces a      *)
(* sorted permutation of the original sequence.  As described in the note  *)
(* "Proving Safety Properties", the proof uses the TLAPS proof system to   *)
(* check the decomposition of the proof into substeps, and to check some   *)
(* of the substeps whose proofs are trivial.                               *)
(*                                                                         *)
(* The version of Quicksort described here sorts a finite sequence of      *)
(* integers.  It is one of the examples in Section 7.3 of "Proving Safety  *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

(***************************************************************************)
(* To aid in model checking the spec, we assume that the sequence to be    *)
(* sorted are elements of a set Values of integers.                        *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* We define PermsOf(s) to be the set of permutations of a sequence s of   *)
(* integers.  In TLA+, a sequence is a function whose domain is the set    *)
(* 1..Len(s).  A permutation of s is the composition of s with a           *)
(* permutation of its domain.  It is defined as follows, where:            *)
(*                                                                         *)
(*  - Automorphisms(S) is the set of all permutations of S, if S is a      *)
(*    finite set--that is all functions f from S to S such that every      *)
(*    element y of S is the image of some element of S under f.            *)
(*                                                                         *)
(*  - f ** g  is defined to be the composition of the functions f and g.   *)
(*                                                                         *)
(* In TLA+, DOMAIN f is the domain of a function f.                        *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

(**************************************************************************)
(* We define Max(S) and Min(S) to be the maximum and minimum,             *)
(* respectively, of a finite, non-empty set S of integers.                *)
(**************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(***************************************************************************)
(* The operator Partitions is defined so that if I is an interval that's a *)
(* subset of 1..Len(s) and p \in Min(I) ..  Max(I)-1, the Partitions(I, p, *)
(* seq) is the set of all new values of sequence seq that a partition      *)
(* procedure is allowed to produce for the subinterval I using the pivot   *)
(* index p.  That is, it's the set of all permutations of seq that leaves  *)
(* seq[i] unchanged if i is not in I and permutes the values of seq[i] for *)
(* i in I so that the values for i =< p are less than or equal to the      *)
(* values for i > p.                                                       *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

(***************************************************************************)
(* Our algorithm has three variables:                                      *)
(*                                                                         *)
(*    seq  : The array to be sorted.                                       *)
(*    seq0 : Holds the initial value of seq, for checking the result.      *)
(*    U    : A set of intervals that are subsets of 1..Len(seq0), an       *)
(*           interval being a nonempty set I of integers that equals      *)
(*           Min(I)..Max(I).                                               *)
(*                                                                         *)
(* The algorithm repeatedly does the following:                            *)
(*                                                                         *)
(*    - Choose an arbitrary interval I in U.                                *)
(*    - If I consists of a single element, remove I from U.                *)
(*    - Otherwise:                                                         *)
(*        - Let I1 be the initial part of I up to a pivot p, and I2 the   *)
(*          remainder.                                                     *)
(*        - Choose newseq that is a permitted partition of seq on I using  *)
(*          pivot p.                                                       *)
(*        - Set seq to newseq.                                             *)
(*        - Replace I in U by I1 and I2.                                   *)
(*                                                                         *)
(* It stops when U is empty.                                                *)
(***************************************************************************)

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

(***************************************************************************)
(* Initial state                                                          *)
(***************************************************************************)
Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

(***************************************************************************)
(* Action a: one step of the algorithm                                    *)
(***************************************************************************)
a ==
  /\ pc = "a"
  /\ IF U # {}
       THEN
         /\ \E I \in U :
              IF Cardinality(I) = 1
                 THEN
                   /\ U' = U \ {I}
                   /\ seq' = seq
                 ELSE
                   /\ \E p \in Min(I)..(Max(I)-1) :
                        LET I1 == Min(I)..p IN
                        LET I2 == (p+1)..Max(I) IN
                        \E newseq \in Partitions(I, p, seq) :
                             /\ seq' = newseq
                             /\ U' = (U \ {I}) \cup {I1, I2}
       ELSE
         /\ pc' = "Done"
         /\ UNCHANGED << seq, U >>
  /\ pc' = "a"
  /\ seq0' = seq0

(***************************************************************************)
(* Allow infinite stuttering on termination                                *)
(***************************************************************************)
Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Postcondition invariant                                                *)
(***************************************************************************)
PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

=============================================================================