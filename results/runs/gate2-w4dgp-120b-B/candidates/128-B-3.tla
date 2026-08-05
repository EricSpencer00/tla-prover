---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int
PermsOf(s) ==
  LET Automorphisms(S) == {f \in [S -> S] :
                             \A y \in S : \E x \in S : f[x] = y}
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  {s ** f : f \in Automorphisms(DOMAIN s)}
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y
Partitions(I, p, s) ==
  {t \in PermsOf(s) :
       /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
       /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}
VARIABLES seq, seq0, U, pc
vars == <<seq, seq0, U, pc>>
Init == /\ seq \in Seq(Values) \ {<<>>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"
a == /\ pc = "a"
     /\ IF U # {}
          THEN /\ \E I \in U :
                    IF Cardinality(I) = 1
                       THEN /\ U' = U \ {I} /\ seq' = seq
                       ELSE /\ \E p \in Min(I)..(Max(I)-1) :
                               LET I1 == Min(I)..p IN
                                 LET I2 == (p+1)..Max(I) IN
                                   \E newseq \in Partitions(I, p, seq) :
                                     /\ seq' = newseq /\ U' = ((U \ {I}) \cup {I1, I2})
                /\ pc' = "a"
          ELSE /\ pc' = "Done" /\ UNCHANGED <<seq, U>>
     /\ seq0' = seq0
Terminating == pc = "Done" /\ UNCHANGED vars
Next == a \/ Terminating
Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)
Termination == <>(pc = "Done")
PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}
DomainPartitions == {DP \subseteq SUBSET (1..Len(seq0)) :
                       /\ (UNION DP) = 1..Len(seq0)
                       /\ \A I \in DP : I = Min(I)..Max(I)
                       /\ \A I, J \in DP : (I # J) => (I \cap J = {})}
RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])
TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
          /\ pc \in {"a", "Done"}
Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)
THEOREM Spec => []PCorrect
  <1>1. Init => Inv
    <2>1. TypeOK
      <3>1. seq \in Seq(Values) \ {<<>>} BY <1>1, Inv, TypeOK
      <3>2. seq0 \in Seq(Values) \ {<<>>} BY <1>1, Inv, TypeOK
      <3>3. U \in SUBSET ((SUBSET (1..Len(seq0))) \ {{}})
        <4>1. Len(seq0) \in Nat /\ Len(seq0) > 0 BY <3>1, EmptySeq, LenProperties
        <4>2. 1..Len(seq0) # {}
        <4>3. QED BY <4>2
        QED BY <4>3, U = {1..Len(seq0)} DEF Init
      <3>4. pc \in {"a", "Done"} BY <1>1, Inv, TypeOK
      <3>5. QED BY <3>1, <3>2, <3>3, <3>4 DEF TypeOK
    <2>2. pc = "Done" => U = {} BY <1>1
    <2>3. UV \in DomainPartitions
      <3>1. UV = {1..Len(seq0)} BY DEF Inv, UV
      <3>2. UV \in SUBSET SUBSET (1..Len(seq0)) BY <3>1
      <3>3. UNION UV = 1..Len(seq0) BY <3>1
      <3>4. 1..Len(seq0) = Min(1..Len(seq0))..Max(1..Len(seq0)) BY <3>1
      <3>5. \A I, J \in UV : I = J BY <3>1
      <3>6. QED BY <3>1..5 DEF DomainPartitions
    <2>4. seq \in PermsOf(seq0)
      <3>1. seq \in PermsOf(seq) BY <1>1
        (*********************************************************************)
        (* This is obvious because the identity function is a permutation of *)
        (* 1..Len(seq).                                                      *)
        (*********************************************************************)
      <3>2. QED BY <3>1
        DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV, PermsOf
    <2>5. UNION UV = 1..Len(seq0) BY <1>1, Inv, TypeOK, DomainPartitions, RelSorted, UV
    <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J) BY <1>1, Inv, TypeOK, DomainPartitions, RelSorted, UV
    <2>7. QED BY <2>1-6 DEF Inv
  <1>2. Inv /\ [Next]_vars => Inv'
    <2>1. CASE a BY <2>1
      <3>1. CASE U # {}
        <4>1. /\ pc = "a" /\ pc' = "a" BY <3>1, a
        <4>2. PICK I \in U : a!2!2!1!(I) BY <3>1, a
        <4>3. CASE Cardinality(I) = 1
          <5>1. /\ U' = U \ {I} /\ seq' = seq /\ seq0' = seq0 /\ pc' = "a"
            BY <4>2, <4>3, a
          <5>2. QED
            <6>1. UV' = UV BY <5>1, <4>1, <4>3
            <6>2. TypeOK' BY <4>1, <4>3, <5>1
              DEF Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
            <6>3. ((pc = "Done") => (U = {}))' BY <4>1, <4>3, <5>1 DEF Inv
            <6>4. (UV \in DomainPartitions)' BY <4>1, <4>3, <5>1, <6>1 DEF Inv, DomainPartitions
            <6>5. (seq \in PermsOf(seq0))' BY <4>1, <4>3, <5>1 DEF Inv, PermsOf
            <6>6. (UNION UV = 1..Len(seq0))' BY <5>1, <6>1 DEF Inv
            <6>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))' BY <4>1, <4>3, <5>1, <6>1 DEF Inv, RelSorted
            <6>8. QED BY <6>2-7 DEF Inv
        <4>4. CASE Cardinality(I) # 1
          <5>1. seq0' = seq0 BY a
          <5>2. PICK p \in Min(I)..(Max(I)-1) :
                 /\ seq' \in Partitions(I, p, seq) /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
            BY <4>2, <4>4, a, DEF I1, I2
          <5>3. /\ /\ Min(I)..p # {} /\ Min(I)..p = Min(Min(I)..p)..Max(Min(I)..p) /\ Min(I)..p \subseteq 1..Len(seq0)
                /\ /\ (p+1)..Max(I) # {} /\ (p+1)..Max(I) = Min((p+1)..Max(I))..Max((p+1)..Max(I)) /\ (p+1)..Max(I) \subseteq 1..Len(seq0)
                /\ Min(I)..p \cap ((p+1)..Max(I)) = {} /\ Min(I)..p \cup ((p+1)..Max(I)) = I
                /\ \A i \in Min(I)..p, j \in (p+1)..Max(I) : (i < j) /\ seq[i] =< seq[j]
            (*********************************************************************)
            (* Since I \in U, invariant Inv implies I is a non-empty subinterval of  *)
            (* 1..Len(seq), and the <4>4 case assumption implies Min(I) < Max(I).  *)
            (* Therefore I1(p) and I2(p) are nonempty subintervals of 1..Len(seq).  *)
            (* It's clear from the definitions of I1(p) and I2(p) that they are    *)
            (* disjoint and union to I.  The final conjunct follows from the       *)
            (* definition of Partitions(I, p, seq).                                 *)
            (*********************************************************************)
          <5>4. /\ Len(seq) = Len(seq') /\ Len(seq) = Len(seq0) BY <5>2, Partitions
          <5>5. UNION U = UNION U' BY <5>2, <5>3
          <5>6. UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)} BY <5>1..5, DEF UV, Len
          <5>7. TypeOK' <6>1. (seq \in Seq(Values) \ {<<>>})' BY <5>2, Partitions
          <5>8. ((pc = "Done") => (U = {}))' BY <4>1
          <5>9. (UV \in DomainPartitions)' <6>1.
            <6>1. UV' \in SUBSET SUBSET (1..Len(seq0')) BY <5>6, <5>3, <5>4, <5>1 DEF Inv
            <6>2. UNION UV' = 1..Len(seq0') BY <5>6, <5>3, <5>4, <5>1 DEF Inv
            <6>3. ASSUME NEW J \in UV' PROVE J = Min(J)..Max(J)
              <7>1. CASE J \in UV BY Inv, DomainPartitions
              <7>2. CASE J = Min(I)..p BY <5>3
              <7>3. CASE J = (p+1)..Max(I) BY <5>3
              <7>4. QED BY <7>1-3, <5>6
            <6>4. ASSUME NEW J \in UV', NEW K \in UV', J # K PROVE J \cap K = {}
              (*********************************************************************)
              (* If J and K are in UV, this follows from Inv.  If one of them is  *)
              (* in UV and the other equals Min(I)..p or (p+1)..Max(I), it follows *)
              (* because Min(I)..p \cup (p+1)..Max(I) = I and I is disjoint from   *)
              (* other elements of UV.  If J and K are Min(I)..p and (p+1)..Max(I), *)
              (* it follows from the definitions of those sets.  By <5>6 this     *)
              (* covers all possibilities.                                         *)
              (*********************************************************************)
            <6>5. QED BY <6>1-4 DEF DomainPartitions, Min, Max
          <5>10. (seq \in PermsOf(seq0))' BY <5>2, PermsOf
          <5>11. (UNION UV = 1..Len(seq0))' BY <5>6, <5>3, <5>1 DEF Inv
          <5>12. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))' BY <5>6, <5>3, <5>1, <5>4, DEF RelSorted
          <5>13. QED BY <5>1, <5>2, <5>3, <5>6, <5>7, <5>8, <5>9, <5>10, <5>11, <5>12 DEF Inv
        <4>5. QED BY <4>3, <4>4
      <3>2. CASE U = {}
        <4>1. QED BY <3>2, a, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
      <3>3. QED BY <3>1, <3>2
    <2>2. CASE UNCHANGED vars
      <3>1. TypeOK' BY <2>2, Inv, TypeOK
      <3>2. ((pc = "Done") => (U = {}))' BY <2>2, Inv
      <3>3. (UV \in DomainPartitions)' BY <2>2, Inv, DomainPartitions
      <3>4. (seq \in PermsOf(seq0))' BY <2>2, Inv, PermsOf
      <3>5. (UNION UV = 1..Len(seq0))' BY <2>2, Inv, UV
      <3>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))' BY <2>2, Inv, RelSorted
      <3>7. QED BY <3>1-6, Inv
    <2>3. QED BY <2>1, <2>2, <2>3, Next
  <1>3. Inv => PCorrect
    <2>1. /\ seq \in PermsOf(seq0) BY <1>1, Inv
       /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
         <3>1. Len(seq) = Len(seq0) /\ Len(seq) \in Nat /\ Len(seq) > 0 BY <2>1, PermsOf, LenProperties
         <3>2. UV = {{i} : i \in 1..Len(seq)} BY U = {} DEF Inv, UV
         <3>3. {p} \in UV /\ {q} \in UV BY <3>2, <3>1
         <3> QED BY <3>3, Inv, RelSorted
    <2>2. QED BY <2>1, PCorrect
  <1>4. QED BY <1>1-3, PTL, Spec
====