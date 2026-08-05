---- MODULE Quicksort ----
(* This module contains an abstract version of the Quicksort sorting          *)
(* algorithm, together with a structured informal proof of its partial          *)
(* correctness property -- namely that if it terminates, it returns a          *)
(* sorted permutation of the original sequence.  The proof uses the TLAPS      *)
(* proof system to check the decomposition of the proof into substeps, and to   *)
(* check some of the substeps whose proofs are trivial.                         *)

EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(**************************************************************************)
(* PermsOf(s) is the set of all permutations of a finite integer sequence s, *)
(* defined as the compositions of s with the permutations of its domain.      *)
(**************************************************************************)
PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

Partitions(I, p, s) == {t \in PermsOf(s) :
    /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
    /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

Init == /\ seq \in Seq(Values) \ {<< >>}
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

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(* The postcondition that Quicksort's partial correctness guarantees.      *)
PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

(* UV is the set of all nonempty subintervals of 1..Len(seq) that are in U,  *)
(* plus every singleton interval inside U's complement; it is used in the   *)
(* invariant.                                                                *)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions == {DP \in SUBSET SUBSET (1..Len(seq0)) :
                       /\ (UNION DP) = 1..Len(seq0)
                       /\ \A I \in DP : I = Min(I)..Max(I)
                       /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])

TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
          /\ pc \in {"a", "Done"}

Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2>2. Inv /\ [Next]_vars => Inv'
    <3> SUFFICES ASSUME Inv,
                     [Next]_vars
                 PROVE  Inv'
      OBVIOUS
    <3>1. CASE a
      <4> USE <3>1
      <4>1. CASE U # {}
        <5>1. /\ pc = "a"
              /\ pc' = "a"
          BY <4>1 DEF a
        <5>2. PICK I \in U : a!2!2!1!(I)
          BY <4>1 DEF a
        <5>3. CASE Cardinality(I) = 1
          <6>1. /\ U' = U \ {I}
                /\ seq' = seq
                /\ seq0' = seq0
            BY <5>2, <5>3 DEF a
          <6>2. QED
            <7>1. UV' = UV
              (*****************************************************************)
              (* Removing a singleton {j} from U adds j to the set of          *)
              (* singletons making UV, so UV is unchanged.                     *)
              (*****************************************************************)
            <7>2. TypeOK'
              BY <5>1, <5>3, <6>1
            <7>3. ((pc = "Done") => (U = {}))'
              BY <5>1, <5>3, <6>1
            <7>4. (UV \in DomainPartitions)'
              BY <5>1, <5>3, <6>1
            <7>5. (seq \in PermsOf(seq0))'
              BY <5>1, <5>3, <6>1
            <7>6. (UNION UV = 1..Len(seq0))'
              BY  <6>1, <7>1
            <7>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
              BY <5>1, <5>3, <6>1, <7>1
            <7>8. QED
              BY <7>2, <7>3, <7>4, <7>5, <7>6, <7>7 DEF Inv
        <5>4. CASE Cardinality(I) # 1
          <6>1. seq0' = seq0
            BY DEF a
          <6>2. PICK p \in Min(I) .. (Max(I)-1) :
                  /\ seq' \in Partitions(I, p, seq)
                  /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
            BY <5>2, <5>4
          <6>3. /\ (Min(I)..p) # {}
                /\ (Min(I)..p) = Min(Min(I)..p)..Max(Min(I)..p)
                /\ (Min(I)..p) \subseteq 1..Len(seq0)
                /\ ((p+1)..Max(I)) # {}
                /\ ((p+1)..Max(I)) = Min((p+1)..Max(I))..Max((p+1)..Max(I))
                /\ ((p+1)..Max(I)) \subseteq 1..Len(seq0)
                /\ (Min(I)..p) \cap ((p+1)..Max(I)) = {}
                /\ (Min(I)..p) \cup ((p+1)..Max(I)) = I
                /\ \A i \in Min(I)..p, j \in (p+1)..Max(I) :
                     (i < j) /\ (seq[i] =< seq[j])
            (*****************************************************************)
            (* Since I is a non-empty subinterval of 1..Len(seq) and          *)
            (* Min(I) < Max(I), its two halves are non-empty subintervals      *)
            (* that partition it, and the final conjunct follows from the      *)
            (* definition of Partitions.                                      *)
            (*****************************************************************)
          <6>4. /\ Len(seq') = Len(seq)
                /\ Len(seq) = Len(seq0)
            BY <6>2, <6>3
          <6>5. UNION U = UNION U'
            BY <6>2, <6>3
          <6>6. UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
            BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF UV
          <6>7. TypeOK'
            <7>1. (seq \in Seq(Values) \ {<<>>})'
              (*****************************************************************)
              (* seq' is a permutation of seq and seq a non-empty sequence of   *)
              (* Values, so seq' is a non-empty sequence of Values.               *)
              (*****************************************************************)
            <7>2. (seq0 \in Seq(Values) \ {<<>>})'
              BY <6>1, <6>2, <6>3, <6>5, <6>6 DEF seq0, Inv, TypeOK
            <7>3. (U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} ))'
              BY <6>2, <6>3, <6>5, <6>6
            <7>4. (pc \in {"a", "Done"})'
              BY <6>1
            <7>5. QED
              BY <7>1, <7>2, <7>3, <7>4 DEF TypeOK, UV
          <6>8. ((pc = "Done") => (U = {}))'
            BY <5>1, <5>4, <6>1
          <6>9. (UV \in DomainPartitions)'
            <7> HIDE DEF I1, I2
            <7>1. UV' \in SUBSET SUBSET (1..Len(seq0'))
              BY <6>6, <6>3, <6>4, <6>1, <6>5  DEF Inv
            <7>2. UNION UV' = 1..Len(seq0')
              BY <6>6, <6>3, <6>4, <6>1, <6>5  DEF Inv
            <7>3. ASSUME NEW J \in UV'
                  PROVE  J = Min(J)..Max(J)
              <8>1. CASE J \in UV
                BY <8>1 DEF Inv, DomainPartitions, UV
              <8>2. CASE J = Min(I)..p
                BY <8>2, <6>3
              <8>3. CASE J = (p+1)..Max(I)
                BY <8>3, <6>3
              <8>4. QED
                BY <8>1, <8>2, <8>3, <6>6
            <7>4. ASSUME NEW J \in UV', NEW K \in UV', J # K
                  PROVE  J \cap K = {}
              (*****************************************************************)
              (* If J and K are both in UV the invariant gives it.  If one is  *)
              (* in UV and the other is one of the new halves, it holds because *)
              (* the halves partition I, which is disjoint from every other     *)
              (* element of UV.  If the two are the two halves themselves, it    *)
              (* holds by construction.  This covers all cases.                 *)
              (*****************************************************************)
            <7>5. QED
              BY <7>1, <7>2, <7>3, <7>4 DEF DomainPartitions, Min, Max
          <6>10. (seq \in PermsOf(seq0))'
            (*****************************************************************)
            (* seq' \in Partitions(I,p,seq) and thus Seq \in PermsOf(seq)      *)
            (* (PermsOf(seq) = PermsOf(seq0) because seq \in PermsOf(seq0)).   *)
            (*****************************************************************)
          <6>11. (UNION UV = 1..Len(seq0))'
            <7> HIDE DEF I1, I2
            <7> QED
              BY <6>6, <6>3, <6>4, <6>1  DEF Inv
          <6>12. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
            <7> SUFFICES ASSUME NEW I_1 \in UV, NEW J \in UV,
                                 (I_1 # J)', NEW i \in I_1, NEW j \in J,
                                 (i < j)'
                             PROVE  (seq[i] =< seq[j])'
              BY DEF RelSorted
            <7> QED
              (*****************************************************************)
              (* The case analysis here mirrors that in <6>9.                    *)
              (*****************************************************************)
          <6>13. QED
            BY <6>7, <6>8, <6>9, <6>10, <6>11, <6>12 DEF Inv
        <5>5. QED
          BY <5>3, <5>4
      <4>2. CASE U = {}
        <5>1. TypeOK' /\ ((pc = "Done") => (U = {}))
                 /\ (UV \in DomainPartitions)
                 /\ (seq \in PermsOf(seq0))
                 /\ (UNION UV = 1..Len(seq0))
                 /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))
          OBVIOUS
      <4>3. QED
        BY <4>1, <4>2
    <3>2. CASE UNCHANGED vars
      <4>1. TypeOK'/ ((pc = "Done") => (U = {}))
                 /\ (UV \in DomainPartitions)
                 /\ (seq \in PermsOf(seq0))
                 /\ (UNION UV = 1..Len(seq0))
                 /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))
          OBVIOUS
      <4>2. QED
        BY <4>1
    <3>3. QED
      BY <3>1, <3>2
  <2>2. Inv => PCorrect
    <3> SUFFICES ASSUME Inv, pc = "Done"
                 PROVE  /\ seq \in PermsOf(seq0)
                        /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
      BY DEF PCorrect
    <3>1. /\ Len(seq) = Len(seq0)
          /\ Len(seq) \in Nat
          /\ Len(seq) > 0
      (*********************************************************************)
      (* By seq \in PermsOf(seq0) and the definition of PermsOf: seq a       *)
      (* non-empty sequence of Values.                                      *)
      (*********************************************************************)
    <3>2. UV = {{i} : i \in 1..Len(seq)}
      BY U = {} DEF Inv, TypeOK, UV
    <3>3. {p} \in UV /\ {q} \in UV
      BY <3>1, <3>2
    <3>4. seq[p] =< seq[q]
      BY <3>3 DEF Inv, RelSorted
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4
    <3>6. QED
      BY <3>5
  <2>3. QED
    BY <2>1, <2>2, PTL DEF Spec
=============================================================================