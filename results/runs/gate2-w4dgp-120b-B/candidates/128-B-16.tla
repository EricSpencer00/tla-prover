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
(* The module sorts a finite sequence of integers.  It is one of the       *)
(* examples in Section 7.3 of "Proving Safety Properties", which is at    *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
  (*************************************************************************)
  (* This statement imports some standard modules, including ones used by  *)
  (* the TLAPS proof system.                                               *)
  (*************************************************************************)

(***************************************************************************)
(* To aid in model checking the spec, we assume that the sequence to be    *)
(* sorted are elements of a set Values of integers.                        *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of permutations of a sequence s of integers.  In  *)
(* TLA+, a sequence is a function whose domain is the set 1..Len(s).  A    *)
(* permutation of s is the composition of s with a permutation of its       *)
(* domain.  It is defined as follows, where:                               *)
(*                                                                         *)
(*  - Automorphisms(S) is the set of all permutations of S, if S is a       *)
(*    finite set--that is, all functions f from S to S such that every       *)
(*    element y of S is the image of some element of S under f.             *)
(*                                                                         *)
(*  - f ** g  is the composition of the functions f and g.                 *)
(*                                                                         *)
(* In TLA+, DOMAIN f is the domain of a function f.                        *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

 (**************************************************************************)
 (* Max(S) and Min(S) are the maximum and minimum, respectively, of a      *)
 (* finite, non-empty set S of integers.                                   *)
 (**************************************************************************)
 Max(S) == CHOOSE x \in S : \A y \in S : x >= y
 Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(***************************************************************************)
(* Partitions(I, p, seq) is the set of new values seq may take over I after   *)
(* a partition step with pivot index p: it is the set of all permutations    *)
(* of seq that leave seq[i] unchanged if i is not in I and permute the      *)
(* values of seq[i] for i in I so that the values for i =< p are less than or *)
(* equal to the values for i > p.                                           *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

(***************************************************************************)
(* Variables:                                                              *)
(*   seq  : the array to be sorted.                                       *)
(*   seq0 : its initial value (for checking the result).                   *)
(*   U    : a set of intervals in 1..Len(seq0); initially the whole       *)
(*          interval.  An interval is removed from U when it is sorted.     *)
(*   pc   : "a" while the algorithm runs, and "Done" once U is empty.      *)
(***************************************************************************)
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
          /\ pc \in {"a", "Done"}

(***************************************************************************)
(* Invariant: while the algorithm runs, the intervals in U partition the   *)
(* whole range of the array, and each interval in the partition is sorted   *)
(* relative to every other interval in it.  Since a non-singleton interval   *)
(* is always split further, it is eventually empty.  While it runs, seq is   *)
(* always a permutation of its initial value.                               *)
(*                                                                         *)
(* Because an empty U means the array is partitioned into singletons,       *)
(* Inv immediately yields that the whole array is sorted.                   *)
(***************************************************************************)
Sorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}
DomainPartitions ==
  {DP \in SUBSET SUBSET (1..Len(seq0)) :
    /\ (UNION DP) = 1..Len(seq0)
    /\ \A I \in DP : I = Min(I)..Max(I)
    /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }
Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => Sorted(I, J)

Init == /\ seq \in Seq(Values) \ {<<>>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"

(***************************************************************************)
(* An interval in U is sorted if it has one element, so a non-empty U is  *)
(* shrunk by the algorithm at every step.                                   *)
(***************************************************************************)
a == /\ pc = "a"
     /\ IF U # {}
          THEN /\ \E I \in U :
                  \/ /\ Cardinality(I) = 1
                       /\ U' = U \ {I}
                       /\ seq' = seq
                  \/ /\ Cardinality(I) # 1
                       /\ \E p \in Min(I) .. (Max(I)-1),
                              I1 = Min(I)..p,
                              I2 = (p+1)..Max(I),
                              newseq \in Partitions(I, p, seq):
                            /\ seq' = newseq
                            /\ U' = (U \ {I}) \cup {I1, I2}
                /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << seq, U >>
     /\ seq0' = seq0

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

PCorrect == (pc = "Done") => /\ seq \in PermsOf(seq0)
                        /\ \A i, j \in 1..Len(seq) : i < j => seq[i] =< seq[j]

=============================================================================