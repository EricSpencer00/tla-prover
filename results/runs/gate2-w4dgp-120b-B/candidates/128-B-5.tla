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
(* sorted permutation of the original sequence.  The proof uses the TLAPS  *)
(* proof system to check the decomposition of the proof into substeps, and *)
(* to check some of the substeps whose proofs are trivial.                 *)
(*                                                                         *)
(* The module sorts a finite sequence of integers.  It is one of the       *)
(* examples in Section 7.3 of "Proving Safety Properties", which is at     *)
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
(* sorted is made of elements drawn from a set Values of integers.         *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of permutations of a sequence s of integers.  In  *)
(* TLA+, a sequence is a function whose domain is the set 1..Len(s).  A      *)
(* permutation of s is the composition of s with a permutation of its       *)
(* domain.  This definition uses:                                          *)
(*                                                                         *)
(*   - AUTOMORPHISMS(S): the set of all permutations of a finite set S.    *)
(*   - The operator ** for function composition.                           *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

(***************************************************************************)
(* Max(S) and Min(S) are the maximum and minimum of a non-empty finite set  *)
(* S of integers.                                                          *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(***************************************************************************)
(* Partitions(I, p, s) is the set of all new values of sequence s that a    *)
(* partition step for subinterval I using pivot index p may produce.  It is  *)
(* the set of permutations of s that leave s[i] unchanged outside I, and     *)
(* rearrange the values inside I so that every value in the left part of I   *)
(* is <= every value in the right part.                                     *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i <= p) /\ (p < j) => (t[i] <= t[j])}

(***************************************************************************)
(* The algorithm has three variables:                                      *)
(*   seq  : the array being sorted.                                        *)
(*   seq0 : the initial value of seq, for checking the result.              *)
(*   U    : the set of intervals still to be sorted.                        *)
(* Start with the whole array as a single interval.                        *)
(* The step repeatedly picks an interval in U and either drops it (if a     *)
(* singleton) or partitions it and replaces it in U by its two parts.       *)
(* The algorithm stops when U is empty.                                     *)
(***************************************************************************)
(* BEGIN TRANSLATION *)
VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \subseteq (SUBSET (1..Len(seq0))) \ {{}} /\ pc \in {"a", "Done"}

\* UV is UV = U \cup {{i} : i \in 1..Len(seq) \ UNION U} as a definition.
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions == {DP \subseteq SUBSET (1..Len(seq0)) :
  /\ (UNION DP) = 1..Len(seq0)
  /\ \A I \in DP : I = Min(I)..Max(I)
  /\ \A I, J \in DP : (I # J) => (I \cap J = {})}

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] <= seq[j])

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)} /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF U = {}
       THEN /\ pc' = "Done" /\ UNCHANGED << seq, seq0, U >>
       ELSE /\ \E I \in U :
              /\ (Cardinality(I) = 1) => (U' = U \ {I} /\ seq' = seq)
              /\ (Cardinality(I) # 1) =>
                   /\ \E p \in Min(I)..(Max(I)-1), newseq \in Partitions(I, p, seq) :
                        /\ seq' = newseq /\ U' = (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
              /\ pc' = "a" /\ seq0' = seq0

Next == a
\* Infinite stuttering on termination is needed to avoid a deadlock.
Terminating == pc = "Done" /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ WF_vars(Terminating)

(\* The postcondition: a terminating run ends with seq a sorted          \*)
(\* permutation of seq0.                                                   \*)
PCorrect == (pc = "Done") => /\ seq \in PermsOf(seq0)
                          /\ \A p, q \in 1..Len(seq) : p < q => seq[p] <= seq[q]

Inv == /\ TypeOK /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

\* The invariant and the postcondition together prove partial correctness.
THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2>1. QED BY DEF Init, Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. CASE a
    <3>1. CASE U # {}
      <4>1. /\ pc = "a" /\ pc' = "a" /\ seq0' = seq0
      <4>2. PICK I \in U : a!2!2!1!(I)
      <4>3. CASE Cardinality(I) = 1
        <5>1. /\ U' = U \ {I} /\ seq' = seq
        <5>2. QED
          <6>1. UV' = UV
            BY <4>2, <4>3, <5>1 DEF UV
          <6>2. QED BY <6>1, <5>1 DEF Inv
      <4>4. CASE Cardinality(I) # 1
        <5>1. seq0' = seq0
        <5>2. PICK p \in Min(I)..(Max(I)-1) :
              /\ seq' \in Partitions(I, p, seq)
              /\ U' = (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
        <5>3. /\ Len(seq) = Len(seq') /\ UNION U = UNION U'
              /\ UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
        <5>4. QED BY <5>2, <5>3 DEF UV
      <3>2. CASE U = {}
        <4>1. QED BY <3>2 DEF Inv, UV
    <2>2. CASE UNCHANGED vars
      <3>1. QED BY <2>2 DEF Inv
  <1>3. Inv => PCorrect
    <2>1. QED BY <1>2, <1>3 DEF PCorrect, Inv
  <1>4. QED BY <1>1, <1>2, <1>3 DEF Spec

=============================================================================