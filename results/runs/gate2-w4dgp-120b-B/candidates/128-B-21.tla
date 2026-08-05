---- MODULE Quicksort
/***************************************************************************
* This module contains an abstract version of the Quicksort algorithm.    *
* If you are not already familiar with that algorithm, you should look it *
* up on the Web and understand how it works--including what the partition *
* procedure does, without worrying about how it does it.  The version     *
* presented here does not specify a partition procedure, but chooses in a *
* single step an arbitrary value that is the result that any partition    *
* procedure may produce.                                                  *
*                                                                         *
* The module also has a structured informal proof of Quicksort's partial  *
* correctness property--namely, that if it terminates, it produces a      *
* sorted permutation of the original sequence.  As described in the note  *
* "Proving Safety Properties", the proof uses the TLAPS proof system to   *
* check the decomposition of the proof into substeps, and to check some   *
* of the substeps whose proofs are trivial.                               *
*                                                                         *
* The module sorts a finite sequence of integers.  It is one of the        *
* examples in Section 7.3 of "Proving Safety Properties", which is at    *
*     http://lamport.azurewebsites.net/tla/proving-safety.pdf              *
***************************************************************************/
/* This statement imports some standard modules, including ones used by the *
 * TLAPS proof system.                                                     */
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

(* To aid in model checking the spec, we assume that the sequence to be     *
 * sorted are elements of a set Values of integers.                        *)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(* We define PermsOf(s) to be the set of permutations of a sequence s of     *
 * integers.  In TLA+, a sequence is a function whose domain is the set      *
 * 1..Len(s).  A permutation of s is the composition of s with a              *
 * permutation of its domain.  In TLA+, DOMAIN f is the domain of a function *
 * f.                                                                       *)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

(* Max(S) and Min(S) are the maximum and minimum, respectively, of a        *
 * finite set S of integers.                                                *)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(* Partitions(I, p, s) is the set of all new values of sequence s that a    *
 * partition procedure is allowed to produce for the subinterval I using    *
 * the pivot index p: the set of all permutations of s that leaves s[i]     *
 * unchanged unless i \in I and permutes the values of s[i] for i \in I so  *
 * that the values for i =< p are less than or equal to the values for i > p. *)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

(* The algorithm has three variables: seq is the array to be sorted, seq0    *
 * holds its initial value, and U is a set of intervals that are subsets of *
 * 1..Len(seq0).  It repeatedly picks an interval I in U and partitions it: *
 * if I is a singleton it is removed from U; otherwise it is split into two *
 * intervals I1 and I2.  It stops when U is empty.                          */
\* BEGIN TRANSLATION
VARIABLES seq, seq0, U, pc
vars == << seq, seq0, U, pc >>

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"
  /\ seq0' = seq0

a ==
  /\ pc = "a"
  /\ IF U # {}
       THEN /\ \E I \in U :
              IF Cardinality(I) = 1
                THEN /\ U' = U \ {I}
                     /\ seq' = seq
                ELSE /\ \E p \in Min(I) .. (Max(I)-1),
                        I1 = Min(I)..p,
                        I2 = (p+1)..Max(I),
                        newseq \in Partitions(I, p, seq):
                     /\ seq' = newseq
                     /\ U' = ((U \ {I}) \cup {I1, I2})
            /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << seq, U >>
  /\ UNCHANGED seq0

Terminating == pc = "Done" /\ UNCHANGED vars
Next == a \/ Terminating
Spec == Init /\ [][Next]_vars /\ WF_vars(a)

TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \subseteq (SUBSET (1..Len(seq0))) \ {{}} /\ pc \in {"a", "Done"}

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}
DomainPartitions ==
  {DP \subseteq SUBSET (1..Len(seq0)) :
     /\ UNION DP = 1..Len(seq0)
     /\ \A I \in DP : I = Min(I)..Max(I)
     /\ \A I, J \in DP : I # J => I \cap J = {}}
RelSorted(I, J) == \A i \in I, j \in J : i < j => seq[i] =< seq[j]

(* UV \in DomainPartitions and seq \in PermsOf(seq0) are the inductive      *
 * invariant that together imply the postcondition PCorrect.               *)
Inv == /\ TypeOK
       /\ pc = "Done" => U = {}
       /\ UV \in DomainPartitions
       /\ UNION UV = 1..Len(seq0)
       /\ seq \in PermsOf(seq0)
       /\ \A I, J \in UV : I # J => RelSorted(I, J)

\* If it terminates, the array is sorted and is a permutation of the input. *
PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
\* The invariant is inductive.                                            *
THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2>1. TypeOK
    <3>1. seq \in Seq(Values) \ {<<>>} BY <2>1 DEF TypeOK
    <3>2. seq0 \in Seq(Values) \ {<<>>} BY <2>1 DEF TypeOK
    <3>3. U \in SUBSET (SUBSET (1..Len(seq0))) \ {{}} BY <2>1 DEF TypeOK
    <3>4. pc \in {"a", "Done"} BY <2>1 DEF TypeOK
    <3>5. uv \in DomainPartitions
      <4>1. UV = {1..Len(seq0)} BY <2>1 DEF UV, Init
      <4>2. UV \in SUBSET SUBSET (1..Len(seq0)) BY <4>1 DEF DomainPartitions
      <4>3. UNION UV = 1..Len(seq0) BY <4>1
      <4>4. \A I \in UV : I = Min(I)..Max(I) BY <4>1
      <4>5. \A I, J \in UV : I # J => I \cap J = {} BY <4>1
      <4>6. QED BY <4>2, <4>3, <4>4, <4>5 DEF DomainPartitions
    <3>6. seq \in PermsOf(seq0)
      <4>1. \E f \in [1..Len(seq0) -> 1..Len(seq0)] : seq = seq0 ** f
        BY <2>1 DEF PermsOf
      <4>2. QED BY <4>1 DEF seq0, seq
    <3>7. \A I, J \in UV : I # J => RelSorted(I, J)
      <4>1. I = {i}, J = {j} => RelSorted(I, J)
        <5>1. ASSUME I = {i}, J = {j}, I # J
             PROVE RelSorted(I, J)
          <6>1. i # j BY <5>1
          <6>2. (\A i \in {i}, j \in {j} : i < j => seq[i] =< seq[j])
                BY <6>1
          <6>3. QED BY <6>2 DEF RelSorted
        <5>2. QED BY <5>1, <6>3
      <4>2. QED BY <4>1, DomainPartitions, UV
    <3>8. QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. CASE a
    <3>1. CASE U # {}
      <4>1. /\ pc = "a" /\ pc' = "a"
        BY <3>1, <3>2 DEF a
      <4>2. PICK I \in U : a!2!2!1!(I) BY <3>1, <3>2 DEF a
      <4>3. CASE Cardinality(I) = 1
        <5>1. /\ U' = U \ {I} /\ seq' = seq /\ seq0' = seq0
          BY <4>2, <4>3 DEF a
        <5>2. /\ \A i \in I : {i} \in UV'
               BY <4>2, <4>3, <5>1 DEF UV
             /\ \A i \in 1..Len(seq) \ (I \cup U) : {i} \in UV'
               BY <4>2, <4>3, <5>1 DEF UV
             /\ \A I_1, J_1 \in UV' : I_1 # J_1 => RelSorted(I_1, J_1)
               BY <5>2, <5>1
             /\ UNION UV' = 1..Len(seq0) BY <5>1
             /\ UV' \in DomainPartitions BY <5>1
             /\ seq' \in PermsOf(seq0) BY <5>1
             /\ TypeOK' BY <5>1, <5>2
        <5>3. QED BY <5>2, <5>1, <5>3 DEF Inv
      <4>4. CASE Cardinality(I) # 1
        <5>1. seq0' = seq0 BY DEF a
        <5>2. PICK p \in Min(I) .. Max(I) - 1 :
                /\ seq' \in Partitions(I, p, seq)
                /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
          BY <4>2, <4>4
        <5>3. /\ Len(seq) = Len(seq') /\ len(seq) = Len(seq0)
               BY <5>2, DEF Partitions, PermsOf
             /\ UNION U' = UNION U BY <5>2
             /\ UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
               BY <5>2, <5>3, DEF UV
             /\ TypeOK' BY <5>2, <5>3
             /\ (\A I_1, J_1 \in UV' : I_1 # J_1 => RelSorted(I_1, J_1))
               BY <5>2, <5>3
             /\ seq' \in PermsOf(seq0) BY <5>2
             /\ UV' \in DomainPartitions BY <5>2, <5>3
             /\ UNION UV' = 1..Len(seq0) BY <5>2, <5>3
        <5>4. QED BY <5>2, <5>3, <5>4, <5>5, <5>6, <5>7 DEF Inv
      <4>5. QED BY <4>3, <4>4
    <3>2. CASE U = {}
      <4>1. /\ pc' = "Done" /\ UNCHANGED << seq, seq0, U >>
        BY <3>2
      <4>2. QED BY <4>1, <3>2, DOMAIN \cup DEF Inv
    <3>3. QED BY <3>1, <3>2
  <2>2. CASE UNCHANGED vars
    <3>1. /\ pc' = pc /\ UNCHANGED << seq, seq0, U >>
      BY <2>2 DEF vars
    <3>2. QED BY <3>1, <2>2, INV_DEF DEF Inv
  <2>3. QED BY <2>1, <2>2 DEF Next
<1>3. Inv => PCorrect
  <2>1. seq \in PermsOf(seq0) BY <1>1, <1>2, <1>3, Def PCorrect, Inv
  <2>2. \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    <3>1. ASSUME NEW p \in 1..Len(seq), NEW q \in 1..Len(seq), p < q
         PROVE seq[p] =< seq[q]
      BY <1>1, <1>2, INV_DEF DEF Inv, RelSorted
    <3>2. QED BY <3>1
  <2>3. QED BY <2>1, <2>2
<1>4. QED BY <1>1, <1>2, <1>3, DEFINITIONS Spec

=============================================================================