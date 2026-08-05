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
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of permutations of a sequence s of integers.      *)
(* A permutation of s is s composed with a permutation of its domain.       *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) ==
        { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(***************************************************************************)
(* Partitions(I, p, s) is the set of all new values of s that a partition  *)
(* procedure is allowed to produce for interval I using pivot p.  Each     *)
(* element of the set is a permutation of s that leaves s[i] unchanged for *)
(* i \notin I and permutes the values of s[i] for i \in I so that the     *)
(* values for i =< p are <= the values for i > p.                          *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
       /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
       /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

Init ==
  /\ seq \in Seq(Values) \ {<< >>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF U # {}
       THEN /\ \E I \in U :
              IF Cardinality(I) = 1
                 THEN /\ U' = U \ {I}
                      /\ seq' = seq
                 ELSE /\ \E p \in Min(I) .. (Max(I)-1) :
                         LET I1 == Min(I)..p IN
                         LET I2 == (p+1)..Max(I) IN
                         \E newseq \in Partitions(I, p, seq) :
                             /\ seq' = newseq
                             /\ U' = ((U \ {I}) \cup {I1, I2})
              /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << seq, U >>
  /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(***************************************************************************)
(* PCorrect is the postcondition: if the sort terminates, seq is a sorted *)
(* permutation of the original sequence.                                    *)
(***************************************************************************)
PCorrect ==
  (pc = "Done") =>
    /\ seq \in PermsOf(seq0)
    /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions ==
  { DP \in SUBSET SUBSET (1..Len(seq0)) :
        /\ (UNION DP) = 1..Len(seq0)
        /\ \A I \in DP : I = Min(I)..Max(I)
        /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
  /\ pc \in {"a", "Done"}

Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (U = {})
  /\ UV \in DomainPartitions
  /\ seq \in PermsOf(seq0)
  /\ UNION UV = 1..Len(seq0)
  /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <2>1. TypeOK
    <3>1. seq \in Seq(Values) \ {<<>>} BY DEF Init, Inv, TypeOK,
         DomainPartitions, RelSorted, UV
    <3>2. seq0 \in Seq(Values) \ {<<>>} BY DEF Init, Inv, TypeOK,
         DomainPartitions, RelSorted, UV
    <3>3. U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
      <4>1. Len(seq0) \in Nat /\ Len(seq0) > 0
        BY <3>1, EmptySeq, LenProperties DEF Init
      <4>2. 1..Len(seq0) # {}
        BY <4>1
      <4>3. QED
        BY <4>2
      <4>4. QED BY <4>2, U = {1..Len(seq0)} DEF Init
    <3>4. pc \in {"a", "Done"} BY DEF Init, Inv, TypeOK,
         DomainPartitions, RelSorted, UV
    <3>5. QED BY <3>1, <3>2, <3>3, <3>4 DEF TypeOK
  <2>2. (pc = "Done") => (U = {}) BY DEF Init
  <2>3. UV \in DomainPartitions
    <3>1. UV = {1..Len(seq0)} BY DEF Inv
    <3>2. UV \in SUBSET SUBSET (1..Len(seq0)) BY <3>1 DEF DomainPartitions
    <3>3. UNION UV = 1..Len(seq0) BY <3>1
    <3>4. 1..Len(seq0) = Min(1..Len(seq0))..Max(1..Len(seq0)) BY <3>1
    <3>5. \A I, J \in UV : I = J BY <3>1
    <3>6. QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF DomainPartitions
  <2>4. seq \in PermsOf(seq0) BY <3>1 DEF Inv
  <2>5. UNION UV = 1..Len(seq0) BY DEF Init, Inv, TypeOK,
       DomainPartitions, RelSorted, UV
  <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J) BY DEF Init, Inv,
       TypeOK, DomainPartitions, RelSorted, UV
  <2>7. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE a
    <3> USE <2>1
    <3>1. CASE U # {}
      <4>1. /\ pc = "a" /\ pc' = "a" BY <3>1 DEF a
      <4>2. PICK I \in U : a!2!2!1!I BY <3>1 DEF a
      <4>3. CASE Cardinality(I) = 1
        <5>1. /\ U' = U \ {I} /\ seq' = seq BY <4>2, <4>3 DEF a
        <5>2. QED
          <6>1. UV' = UV BY <4>1, <4>3, <5>1 DEF Inv, TypeOK,
               DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>2. TypeOK' BY <4>1, <4>3, <5>1 DEF Inv, TypeOK,
               DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>3. ((pc = "Done") => (U = {}))' BY <4>1, <4>3, <5>1
               DEF Inv, TypeOK, DomainPartitions, PermsOf, RelSorted,
               Min, Max, UV
          <6>4. UV' \in DomainPartitions BY <4>1, <4>3, <5>1
               DEF Inv, TypeOK, DomainPartitions
          <6>5. (seq \in PermsOf(seq0))' BY <4>1, <4>3, <5>1
               DEF Inv, TypeOK, PermsOf
          <6>6. UNION UV = 1..Len(seq0) BY <5>1, <6>1 DEF Inv
          <6>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))' BY
               <4>1, <4>3, <5>1, <6>1 DEF Inv, TypeOK, RelSorted
          <6>8. QED BY <6>2, <6>3, <6>4, <6>5, <6>6, <6>7 DEF Inv
        <5>3. CASE Cardinality(I) # 1
          <6> DEFINE I1(p) == Min(I)..p
                 I2(p) == (p+1)..Max(I)
          <6>1. seq0' = seq0 BY DEF a
          <6>2. PICK p \in Min(I) .. (Max(I)-1) :
                    /\ seq' \in Partitions(I, p, seq)
                    /\ U' = ((U \ {I}) \cup {I1(p), I2(p)})
            BY <4>2, <4>4
          <6>3. /\ /\ I1(p) # {} /\ I1(p) = Min(I1(p))..Max(I1(p))
                    /\ I1(p) \subseteq 1..Len(seq0)
               /\ /\ I2(p) # {} /\ I2(p) = Min(I2(p))..Max(I2(p))
                    /\ I2(p) \subseteq 1..Len(seq0)
               /\ I1(p) \cap I2(p) = {}
               /\ I1(p) \cup I2(p) = I
               /\ \A i \in I1(p), j \in I2(p) : (i < j) /\ (seq[i] =< seq[j])
            BY <6>2, <6>3
          <6>4. /\ Len(seq) = Len(seq') /\ Len(seq) = Len(seq0) BY <6>2
          <6>5. UNION U = UNION U' BY <6>2, <6>3
          <6>6. UV' = (UV \ {I}) \cup {I1(p), I2(p)} BY <6>1, <6>2, <6>3,
               <6>4, <6>5 DEF UV
          <6>7. TypeOK' BY <6>1, <6>2, <6>3, <6>4, <6>5, <6>6,
               DEF TypeOK, Inv, UV, PermsOf, RelSorted, Min, Max
          <6>8. ((pc = "Done") => (U = {}))' BY <4>1
          <6>9. UV' \in DomainPartitions
            <7> HIDE DEF I1, I2
            <7>1. UV' \in SUBSET SUBSET (1..Len(seq0')) BY <6>6, <6>3, <6>4,
                 <6>1 DEF Inv
            <7>2. UNION UV' = 1..Len(seq0') BY <6>6, <6>3, <6>4, <6>1 DEF Inv
            <7>3. ASSUME NEW J \in UV' PROVE J = Min(J)..Max(J)
              <8>1. CASE J \in UV BY <8>1 DEF Inv, DomainPartitions
              <8>2. CASE J = I1(p) BY <8>2, <6>3
              <8>3. CASE J = I2(p) BY <8>3, <6>3
              <8>4. QED BY <8>1, <8>2, <8>3, <6>6
            <7>4. ASSUME NEW J \in UV', NEW K \in UV', J # K
                 PROVE J \cap K = {}
              (***********************************************************)
              (* If J and K are in UV, this follows from Inv.  If one is  *)
              (* in UV and the other equals I1(p) or I2(p), it follows     *)
              (* because I1(p) \cup I2(p) = I and I is disjoint from other   *)
              (* UV elements.  If J and K are I1(p) and I2(p), it follows   *)
              (* from the definitions of I1(p) and I2(p).  By <6>6, this    *)
              (* covers all possibilities.                                *)
              (***********************************************************)
              <8>1. CASE J \in UV BY <8>1 DEF Inv, DomainPartitions
              <8>2. CASE J = I1(p) BY <8>2, <6>3
              <8>3. CASE J = I2(p) BY <8>3, <6>3
              <8>4. QED BY <8>1, <8>2, <8>3, <6>6
            <7>5. QED BY <7>1, <7>2, <7>3, <7>4 DEF DomainPartitions
          <6>10. (seq \in PermsOf(seq0))' BY <6>2, <6>3
          <6>11. UNION UV = 1..Len(seq0) BY <6>6, <6>3, <6>1 DEF Inv
          <6>12. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
            <7> SUFFICES ASSUME NEW I_1 \in UV', NEW J \in UV',
                            I_1 # J', NEW i \in I_1', NEW j \in J',
                            i < j' PROVE (seq[i] =< seq[j])'
              BY DEF RelSorted
            <7> QED
              (***********************************************************)
              (* If I_1 and J are in UV, this follows from Inv.  If one      *)
              (* equals I1(p) or I2(p) and the other is in UV, it follows   *)
              (* from Inv because RelSorted(I, K) and RelSorted(K, I) hold  *)
              (* for all K \in UV and I1(p), I2(p) are subsets of I.  If I_1 *)
              (* and J are I1(p) and I2(p), it follows from the definition   *)
              (* of I1 and I2.                                             *)
              (***********************************************************)
          <6>13. QED BY <6>7, <6>8, <6>9, <6>10, <6>11, <6>12 DEF Inv
        <5>4. QED BY <5>2, <5>3, <5>4, <5>5, <5>6, <5>7 DEF Inv
      <4>5. QED BY <4>3, <4>4
    <3>2. CASE U = {}
      <4> USE <3>2 DEF a, Inv, TypeOK, DomainPartitions, PermsOf,
        RelSorted, Min, Max, UV
      <4>1. TypeOK' OBVIOUS
      <4>2. ((pc = "Done") => (U = {}))' OBVIOUS
      <4>3. UV' \in DomainPartitions OBVIOUS
      <4>4. (seq \in PermsOf(seq0))' OBVIOUS
      <4>5. (UNION UV = 1..Len(seq0))' OBVIOUS
      <4>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))' OBVIOUS
      <4>7. QED BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF Inv
    <3>3. QED BY <3>1, <3>2
  <2>2. CASE UNCHANGED vars
    <3>1. TypeOK' BY <2>2 DEF vars, Inv, TypeOK, DomainPartitions,
         PermsOf, RelSorted, Min, Max
    <3>2. ((pc = "Done") => (U = {}))' BY <2>2 DEF vars, Inv, TypeOK,
         DomainPartitions, PermsOf, RelSorted, Min, Max
    <3>3. UV' \in DomainPartitions BY <2>2 DEF vars, Inv, TypeOK,
         DomainPartitions, PermsOf, RelSorted, Min, Max, UV
    <3>4. (seq \in PermsOf(seq0))' BY <2>2 DEF vars, Inv, TypeOK,
         DomainPartitions, PermsOf, RelSorted, Min, Max
    <3>5. UNION UV = 1..Len(seq0) BY <2>2 DEF vars, Inv, TypeOK,
         DomainPartitions, PermsOf, RelSorted, Min, Max, UV
    <3>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))' BY <2>2
         DEF vars, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted,
         Min, Max, UV
    <3>7. QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Inv
  <2>3. QED BY <2>1, <2>2 DEF Next
<1>3. Inv => PCorrect
  <2> SUFFICES ASSUME Inv, pc = "Done" PROVE /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    BY DEF PCorrect
  <2>1. seq \in PermsOf(seq0) BY DEF Inv
  <2>2. \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    <3> SUFFICES ASSUME NEW p \in 1..Len(seq), NEW q \in 1..Len(seq),
                 p < q PROVE seq[p] =< seq[q] OBVIOUS
    <3>1. /\ Len(seq) = Len(seq0) /\ Len(seq) \in Nat /\ Len(seq) > 0
      BY <3>2, <2>1, PermsOf, LenProperties
    <3>2. UV = {{i} : i \in 1..Len(seq)} BY U = {} DEF Inv, TypeOK, UV
    <3>3. {p} \in UV /\ {q} \in UV BY <3>1, <3>2
    <3> QED BY <3>3 DEF Inv, RelSorted
  <2>3. QED BY <2>1, <2>2
<1>4. QED BY <1>1, <1>2, <1>3 DEF Spec
=============================================================================