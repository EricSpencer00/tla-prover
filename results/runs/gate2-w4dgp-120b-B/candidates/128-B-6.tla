---- MODULE Quicksort ----
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
  (*************************************************************************)
  (* This statement imports some standard modules, including ones used by  *)
  (* the TLAPS proof system.                                               *)
  (*************************************************************************)

(***************************************************************************)
(* To aid in model checking, we assume the sequence's elements come from a  *)
(* set Values of integers.                                                  *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* PermsOf(s) is the set of permutations of a sequence s.  A permutation   *)
(* of s is s composed with a permutation of its domain.                     *)
(***************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(***************************************************************************)
(* Partitions(I, p, s) is the set of values seq may take after partitioning *)
(* interval I with pivot p: seq is unchanged off I, and values in I left of *)
(* p are <= those right of p.                                             *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
     /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
     /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

Init ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

a == /\ pc = "a"
     /\ IF U # {}
           THEN /\ \E I \in U:
                     IF Cardinality(I) = 1
                        THEN /\ U' = U \ {I}
                             /\ seq' = seq
                        ELSE /\ \E p \in Min(I) .. (Max(I)-1):
                                  LET I1 == Min(I)..p IN
                                    LET I2 == (p+1)..Max(I) IN
                                      \E newseq \in Partitions(I, p, seq):
                                        /\ seq' = newseq
                                        /\ U' = ((U \ {I}) \cup {I1, I2})
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << seq, U >>
     /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

(***************************************************************************)
(* PCorrect: if Quicksort terminates, seq is a sorted permutation of seq0. *)
(***************************************************************************)
PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

DomainPartitions == {DP \in SUBSET SUBSET (1..Len(seq0)) :
  /\ (UNION DP) = 1..Len(seq0)
  /\ \A I \in DP : I = Min(I)..Max(I)
  /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

TypeOK ==
  /\ seq \in Seq(Values) \ {<<>>}
  /\ seq0 \in Seq(Values) \ {<<>>}
  /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
  /\ pc \in {"a", "Done"}

UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

Inv == /\ TypeOK
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
    <3>1. seq \in Seq(Values) \ {<<>>} /\ seq0 \in Seq(Values) \ {<<>>}
      BY DEF Init, TypeOK
    <3>2. U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
      BY <3>1, Init, TypeOK
    <3>3. pc \in {"a", "Done"}
      BY <3>1, Init, TypeOK
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF TypeOK
  <2>2. (pc = "Done") => (U = {})
    BY Init
  <2>3. UV \in DomainPartitions
    <3>1. UV = {1..Len(seq0)}
      BY DEF UV, Init
    <3>2. QED
      BY <3>1 DEF DomainPartitions
  <2>4. seq \in PermsOf(seq0)
    <3>1. QED
      BY DEF Init \* , Inv, TypeOK, DomainPartitions, RelSorted, UV, PermsOf
  <2>5. UNION UV = 1..Len(seq0)
    BY Init, UV, TypeOK
  <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J)
    BY Init, UV, TypeOK
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE a
    <3> USE <2>1
    <3>1. CASE U # {}
      <4>1. /\ pc = "a" /\ pc' = "a"
            /\ \E I \in U :
                 /\ IF Cardinality(I) = 1
                      THEN /\ U' = U \ {I}
                           /\ seq' = seq
                      ELSE /\ \E p \in Min(I) .. (Max(I)-1):
                                LET I1 == Min(I)..p IN
                                  LET I2 == (p+1)..Max(I) IN
                                    \E newseq \in Partitions(I, p, seq):
                                      /\ seq' = newseq
                                      /\ U' = ((U \ {I}) \cup {I1, I2})
                /\ seq0' = seq0
      <4>2. CASE Cardinality(I) = 1
        <5>1. UV' = UV
          BY <4>1, <4>2
        <5>2. QED
          <6>1. TypeOK'
            BY <4>1, <4>2
              DEF Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>2. ((pc = "Done") => (U = {}))'
            BY <4>1, <4>2
              DEF Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>3. (UV \in DomainPartitions)'
            BY <4>1, <4>2
              DEF Inv, TypeOK, DomainPartitions
          <6>4. (seq \in PermsOf(seq0))'
            BY <4>1, <4>2
              DEF Inv, TypeOK, PermsOf
          <6>5. (UNION UV = 1..Len(seq0))'
            BY <4>1, <4>2, <5>1
              DEF Inv
          <6>6. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
            BY <4>1, <4>2, <5>1
              DEF Inv, TypeOK, RelSorted
          <6>7. QED
            BY <6>1, <6>2, <6>3, <6>4, <6>5, <6>6 DEF Inv
      <4>3. CASE Cardinality(I) # 1
        <5>1. seq0' = seq0
          BY DEF a
        <5>2. PICK p \in Min(I) .. (Max(I)-1) :
                /\ seq' \in Partitions(I, p, seq)
                /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
          BY <4>1, <4>3
        <5>3. /\ Len(seq) = Len(seq')
              /\ UNION U = UNION U'
              /\ UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
          BY <5>2
        <5>4. TypeOK'
          <6>1. (seq \in Seq(Values) \ {<<>>})'
            BY <5>2, <5>3, DEF a, PermsOf, Values
          <6>2. (seq0 \in Seq(Values) \ {<<>>})'
            BY <5>1, <5>3
          <6>3. (U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} ))'
            <7>1. /\ (U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)} \subseteq
                     SUBSET (1..Len(seq0))
                  /\ ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}) # {}
                BY <5>3
            <7>2. QED
              BY <5>3
          <6>4. (pc \in {"a", "Done"})'
            BY <4>1
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF TypeOK
        <5>5. ((pc = "Done") => (U = {}))'
          BY <4>1
        <5>6. (UV \in DomainPartitions)'
          <6>1. UV' \in SUBSET SUBSET (1..Len(seq0))
            BY <5>3, <5>2
          <6>2. UNION UV' = 1..Len(seq0)
            BY <5>3, <5>2
          <6>3. ASSUME NEW J \in UV'
                PROVE  J = Min(J)..Max(J)
            <7>1. CASE J \in UV
              BY <7>1
            <7>2. CASE J = Min(I)..p
              BY <7>2, <5>3
            <7>3. CASE J = (p+1)..Max(I)
              BY <7>3, <5>3
            <7>4. QED
              BY <7>1, <7>2, <7>3, <5>3
          <6>4. ASSUME NEW J \in UV', NEW K \in UV', J # K
                PROVE  J \cap K = {}
            (*******************************************************************)
            (* This follows from the facts that I is an interval and is         *)
            (* partitioned into the two disjoint subintervals Min(I)..p and       *)
            (* (p+1)..Max(I).                                                    *)
            (*******************************************************************)
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF DomainPartitions, Min, Max
        <5>7. (seq \in PermsOf(seq0))'
          (*******************************************************************)
          (* By <5>2 and definition of Partitions, seq' \in PermsOf(seq), and   *)
          (* seq \in PermsOf(seq0).                                            *)
          (*******************************************************************)
        <5>8. (UNION UV = 1..Len(seq0))'
          <6> QED
            BY <5>3, <5>1 DEF Inv
        <5>9. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
          <6> SUFFICES ASSUME NEW I_1 \in UV, NEW J \in UV,
                            (I_1 # J), NEW i \in I_1, NEW j \in J,
                            (i < j)
                        PROVE  (seq[i] =< seq[j])'
            BY DEF RelSorted
          <6> QED
            (*******************************************************************)
            (* This follows from RelSorted holding on UV and the fact that the   *)
            (* new interval I is partitioned into the two subintervals Min(I)..p *)
            (* and (p+1)..Max(I).                                               *)
            (*******************************************************************)
        <5>10. QED
          BY <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9 DEF Inv
      <4>4. QED
        BY <4>2, <4>3
    <3>2. CASE U = {}
      <4> USE <3>2 DEF a, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, UV
      <4>1. TypeOK'
        OBVIOUS
      <4>2. ((pc = "Done") => (U = {}))'
        OBVIOUS
      <4>3. (UV \in DomainPartitions)'
        OBVIOUS
      <4>4. (seq \in PermsOf(seq0))'
        OBVIOUS
      <4>5. (UNION UV = 1..Len(seq0))'
        OBVIOUS
      <4>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))'
        OBVIOUS
      <4>7. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF Inv
    <3>3. QED
      BY <3>1, <3>2
  <2>2. CASE UNCHANGED vars
    <3>1. TypeOK'
      BY <2>2 DEF Inv, TypeOK
    <3>2. ((pc = "Done") => (U = {}))'
      BY <2>2 DEF Inv
    <3>3. (UV \in DomainPartitions)'
      BY <2>2 DEF Inv
    <3>4. (seq \in PermsOf(seq0))'
      BY <2>2 DEF Inv
    <3>5. (UNION UV = 1..Len(seq0))'
      BY <2>2 DEF Inv
    <3>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))'
      BY <2>2 DEF Inv
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Inv
  <2>3. QED
    BY <2>1, <2>2 DEF Next
<1>3. Inv => PCorrect
  <2> SUFFICES ASSUME Inv, pc = "Done"
               PROVE /\ seq \in PermsOf(seq0)
                     /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    BY DEF PCorrect
  <2>1. seq \in PermsOf(seq0)
    BY DEF Inv
  <2>2. \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    <3> SUFFICES ASSUME NEW p \in 1..Len(seq), NEW q \in 1..Len(seq), p < q
                 PROVE seq[p] =< seq[q]
      OBVIOUS
    <3>1. Len(seq) = Len(seq0)
      BY DEF Inv
    <3>2. UV = {{i} : i \in 1..Len(seq)}
      BY UNCHANGED U DEF Inv
    <3>3. {p} \in UV /\ {q} \in UV
      BY <3>1, <3>2
    <3> QED
      BY <3>3 DEF Inv, RelSorted
  <2>3. QED
    BY <2>1, <2>2
<1>4. QED
  BY <1>1, <1>2, <1>3
=============================================================================