---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

PermsOf(s) ==
  LET Automorphisms(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { s ** f : f \in Automorphisms(DOMAIN s) }

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

Partitions(I, p, s) ==
  {t \in PermsOf(s) : 
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

Init == (* Global variables *)
        /\ seq \in Seq(Values) \ {<< >>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"

UV == U \cup {{i} : i \in 1..Len(seq) \ U}

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
                                        /\ U' = ((U \ {I}) \cap {I1, I2})
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << seq, U >>
     /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

PCorrect == (pc = "Done") => 
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q] 

UV == U \cup {{i} : i \in 1..Len(seq) \ U}

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
  <2>1. TypeOK
    <3>1. seq \in Seq(Values) \ {<<>>} 
      BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
    <3>2. seq0 \in Seq(Values) \ {<<>>}
      BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
    <3>3. U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
      <4>1. Len(seq0) \in Nat  /\ Len(seq0) > 0
        BY <3>1, EmptySeq, LenProperties DEF Init
      <4>2. 1..Len(seq0) # {}
        BY <4>1
      <4>3. QED
       BY <4>2, U = {1..Len(seq0)} DEF Init
    <3>4. pc \in {"a", "Done"}
      BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF TypeOK   
  <2>2. pc = "Done" => U = {}
    BY DEF Init
  <2>3. UV \in DomainPartitions
    <3>1. UV = {1..Len(seq0)}
      (*********************************************************************)
      (* Follows easily from definition of UV, seq0 = seq, and seq a       *)
      (* non-empty sequence.                                               *)
      (*********************************************************************)
    <3>2. UV \in SUBSET SUBSET (1..Len(seq0))
      BY <3>1 DEF Inv
    <3>3. (UNION UV) = 1..Len(seq0)
      BY <3>1
    <3>4. 1..Len(seq0) = Min(1..Len(seq0))..Max(1..Len(seq0))
      (*********************************************************************)
      (* Because seq0 = seq and seq a non-empty sequence imply Len(seq0) a *)
      (* positive natural number.                                          *)
      (*********************************************************************)
    <3>5. \A I, J \in UV : I = J
      BY <3>1
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF DomainPartitions
  <2>4. seq \in PermsOf(seq0)
    <3>1. seq \in PermsOf(seq)
      (*********************************************************************)
      (* This is obvious because the identity function is a permutation of *)
      (* 1..Len(seq).                                                      *)
      (*********************************************************************)
    <3>2. QED
      BY <3>1 DEF Init \* , Inv, TypeOK, DomainPartitions, RelSorted, UV, PermsOf
  <2>5. UNION UV = 1..Len(seq0)
    BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
  <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J)
    BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE a
    <3> USE <2>1
    <3>1. CASE U # {}
      <4>1. /\ pc = "a"
            /\ pc' = "a"
        BY <3>1 DEF a
      <4>2. PICK I \in U : a!2!2!1!(I)
        (*******************************************************************)
        (* a!2!2!1(I) is the formula following `\E I \in U:' in the        *)
        (* definition of a.                                                *)
        (*******************************************************************)
        BY <3>1 DEF a
      <4>3. CASE Cardinality(I) = 1
        <5>1. /\ U' = U \ {I}
              /\ seq' = seq
              /\ seq0' = seq0
          BY <4>2, <4>3 DEF a
        <5>2. QED
          <6>1. UV' = UV
            (***************************************************************)
            (* The action removes a singleton set {j} from U, which adds j *)
            (* to the set {{i} : i \in 1..Len(seq) \ UNION U}, thereby     *)
            (* keeping it in UV.                                           *)
            (***************************************************************)
          <6>2. TypeOK'
            BY <4>1, <4>3, <5>1 
            DEF Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>3. ((pc = "Done") => (U = {}))'
            BY <4>1, <4>3, <5>1 
            DEF Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>4. (UV \in DomainPartitions)'
            BY <4>1, <4>3, <5>1, <6>1
            DEF Inv, TypeOK, DomainPartitions 
          <6>5. (seq \in PermsOf(seq0))'
            BY <4>1, <4>3, <5>1 
            DEF Inv, TypeOK,  PermsOf 
          <6>6. (UNION UV = 1..Len(seq0))'
            BY  <5>1, <6>1 DEF Inv 
          <6>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
            BY <4>1, <4>3, <5>1, <6>1
            DEF Inv, TypeOK, RelSorted 
          <6>8. QED
            BY <6>2, <6>3, <6>4, <6>5, <6>6, <6>7 DEF Inv          
      <4>4. CASE Cardinality(I) # 1 
        <5>1. seq0' = seq0
          BY DEF a
        <5> DEFINE I1(p) == Min(I)..p 
                   I2(p) == (p+1)..Max(I)
        <5>2. PICK p \in Min(I) .. (Max(I)-1) : 
                    /\ seq' \in Partitions(I, p, seq)
                    /\ U' = ((U \ {I}) \cup {I1(p), I2(p)})
          BY <4>2, <4>4
        <5>3. /\ /\ I1(p) # {} 
                 /\ I1(p) = Min(I1(p)).. Max(I1(p))
                 /\ I1(p) \subseteq 1..Len(seq0)
              /\ /\ I2(p) # {} 
                 /\ I2(p) = Min(I2(p)).. Max(I2(p))
                 /\ I2(p) \subseteq 1..Len(seq0)
              /\ I1(p) \cap I2(p) = {}
              /\ I1(p) \cup I2(p) = I
              /\ \A i \in I1(p), j \in I2(p) : (i < j) /\ (seq[i] =< seq[j])
          (****************************************************************)
          (* Since I is in U, invariant Inv implies I is a non-empty       *)
          (* subinterval of 1..Len(seq), and the <4>4 case assumption      *)
          (* implies Min(I) < Max(I).  Therefore I1(p) and I2(p) are       *)
          (* nonempty subintervals of 1..Len(seq).  It's clear from the    *)
          (* definitions of I1(p) and I2(p) that they are disjoint sets    *)
          (* whose union is I.  The final conjunct follows from the        *)
          (* definition of Partitions(I, p, seq).                          *)
          (*****************************************************************) 
        <5>4. /\ Len(seq) = Len(seq')
              /\ Len(seq) = Len(seq0)
          (*****************************************************************)
          (* By <5>2 and definition of Partitions.                         *)
          (*****************************************************************)
        <5>5. UNION U = UNION U'
          (*****************************************************************)
          (* By <5>2 and <5>3, since the action removes I from U and adds  *)
          (* I1(p) and I2(p) to it.                                        *)
          (*****************************************************************)
        <5>6. UV' = (UV \ {I}) \cup {I1(p), I2(p)}
          BY <5>1, <5>2, <5>3, <5>4, <5>5 DEF UV
          (*****************************************************************)
          (* By <5>2, <5>3, and definition of UV, since Len(seq) =         *)
          (* Len(seq').                                                   *)
          (*****************************************************************)        
        <5>7. TypeOK'
          <6>1. (seq \in Seq(Values) \ {<<>>})'
            (***************************************************************)
            (* By <5>2 and definitions of Partitions and PermsOf, since    *)
            (* seq a non-empty sequence of Values implies PermsOf(seq) is  *)
            (* one too.                                                    *)
            (***************************************************************)
          <6>2. (seq0 \in Seq(Values) \ {<<>>})'
            BY <5>1 DEF TypeOK, Inv
          <6>3. (U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} ))'
            (***************************************************************)
            (* By <5>2 and <5>3.                                           *)
            (***************************************************************)
          <6>4. (pc \in {"a", "Done"})'
            BY <4>1
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF TypeOK
        <5>8. ((pc = "Done") => (U = {}))'
          BY <4>1
        <5>9. (UV \in DomainPartitions)'
          <6> HIDE DEF I1, I2
          <6>1. UV' \in SUBSET SUBSET (1..Len(seq0'))
            BY <5>6, <5>3, <5>4, <5>1  DEF Inv
          <6>2. UNION UV' = 1..Len(seq0')
            BY <5>6, <5>3, <5>4, <5>1  DEF Inv
          <6>3. ASSUME NEW J \in UV' 
                PROVE  J = Min(J)..Max(J)
            <7>1. CASE J \in UV
              BY <7>1 DEF Inv, DomainPartitions
            <7>2. CASE J = I1(p)
              BY <7>2, <5>3
            <7>3. CASE J = I2(p)
              BY <7>3, <5>3
            <7>4. QED
              BY <7>1, <7>2, <7>3, <5>6
          <6>4. ASSUME NEW J \in UV', NEW K \in UV', J # K 
                PROVE  J \cap K = {}
            (***************************************************************)
            (* If J and K are in UV, then this follows from Inv.  If one   *)
            (* of them is in UV and the other equals I1(p) or I2(p), it    *)
            (* follows because I1(p) \cup I2(p) = I and I is disjoint from *)
            *\ NEW K \in UV', J # K 
                PROVE  J \cap K = {}
            (*****************************************************************)
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF DomainPartitions, Min, Max
        <5>10. (seq \in PermsOf(seq0))'
          (*****************************************************************)
          (* By <5>2 and definition of Partitions, seq' \in PermsOf(seq),  *)
          (* and seq \in PermsOf(seq0) implies PermsOf(seq) =              *)
          (* PermsOf(seq0).                                                *)
          (*****************************************************************)
        <5>11. (UNION UV = 1..Len(seq0))'
          <6> HIDE DEF I1, I2
          <6> QED
            BY <5>6, <5>3, <5>4, <5>1  DEF Inv
        <5>12. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
          <6> SUFFICES ASSUME NEW I_1 \in UV', NEW J \in UV',
                              (I_1 # J)',
                              NEW i \in I_1', NEW j \in J',
                              (i < j)'
                       PROVE  (seq[i] =< seq[j])'
            BY DEF RelSorted
          <6> QED
            (***************************************************************)
            (* IF I_1 and J are in UV, then this follows from Inv.  If one *)
            (* of them is in UV and the other equals I1(p) or I2(p), it    *)
            (* follows from Inv because RelSorted(I, K) and RelSorted(K,   *)
            (* I) holds for all K in UV and I1(p) and I2(p) are subsets of *)
            (* I.  If I_1 and J are I1(p) and I2(p), then it follows from  *)
            (* the definitions of I1 and I2.  By <5>6, this covers all     *)
            (* possibilities.                                              *)
            (***************************************************************)
        <5>13. QED
          BY <5>7, <5>8, <5>9, <5>10, <5>11, <5>12 DEF Inv
      <4>5. QED
        BY <4>3, <4>4      
    <3>2. CASE U = {}
      <4> USE <3>2 DEF a, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
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
      BY <2>2 DEF vars, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max
    <3>2. ((pc = "Done") => (U = {}))'
      BY <2>2 DEF vars, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max
    <3>3. (UV \in DomainPartitions)'
      BY <2>2 DEF vars, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
    <3>4. (seq \in PermsOf(seq0))'
      BY <2>2 DEF vars, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max
    <3>5. (UNION UV = 1..Len(seq0))'
      BY <2>2 DEF vars, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
    <3>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))'
      BY <2>2 DEF vars, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Inv    
  <2>3. QED
    BY <2>1, <2>2 DEF Next
<1>3. Inv => PCorrect
  <2> SUFFICES ASSUME Inv,
                      pc = "Done"
               PROVE  /\ seq \in PermsOf(seq0)
                      /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    BY DEF PCorrect
  <2>1. seq \in PermsOf(seq0)
    BY DEF Inv
  <2>2. \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    <3> SUFFICES ASSUME NEW p \in 1..Len(seq), NEW q \in 1..Len(seq),
                        p < q
                 PROVE  seq[p] =< seq[q]
      OBVIOUS
    <3>1. /\ Len(seq) = Len(seq0)
          /\ Len(seq) \in Nat
          /\ Len(seq) > 0
      (*********************************************************************)
      (* By seq \in PermsOf(seq0), seq a non-empty sequence, and           *)
      (* definition of PermsOf.                                            *)
      (*********************************************************************)
    <3>2. UV = {{i} : i \in 1..Len(seq)}
      BY U = {} DEF Inv, TypeOK, UV
    <3>3. {p} \in UV /\ {q} \in UV
      BY <3>1, <3>2
    <3> QED
      BY <3>3 DEF Inv, RelSorted
  <2>3. QED
    BY <2>1, <2>2
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
====