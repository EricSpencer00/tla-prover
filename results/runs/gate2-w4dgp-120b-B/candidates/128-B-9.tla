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

Init ==
  /\ seq \in Seq(Values) \ {<< >>}
  /\ seq0 = seq
  /\ U = {1..Len(seq)}
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ (IF U # {}
        THEN /\ \E I \in U :
                IF Cardinality(I) = 1
                  THEN /\ U' = U \ {I}
                       /\ seq' = seq
                  ELSE /\ \E p \in Min(I) .. (Max(I)-1) :
                         LET I1 == Min(I)..p IN
                           LET I2 == (p+1)..Max(I) IN
                             /\ \E newseq \in Partitions(I, p, seq) :
                                  /\ seq' = newseq
                                  /\ U' = ((U \ {I}) \cup {I1, I2})
        ELSE /\ pc' = "Done" /\ UNCHANGED << seq, U >>)
  /\ seq0' = seq0

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

PCorrect == (pc = "Done") =>
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]

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
  <2> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <2>1. TypeOK
    <3>1. seq \in Seq(Values) \ {<<>>} BY <2>1, Inv, TypeOK
    <3>2. seq0 \in Seq(Values) \ {<<>>} BY <2>1, Inv, TypeOK
    <3>3. U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
      <4>1. Len(seq0) \in Nat /\ Len(seq0) > 0 BY <3>1, EmptySeq, LenProperties
      <4>2. 1..Len(seq0) # {} BY <4>1
      <4>3. QED BY <4>2
      BY <4>3, U = {1..Len(seq0)} DEF Init
    <3>4. pc \in {"a", "Done"} BY <2>1, Inv, TypeOK
    <3>5. QED BY <3>1, <3>2, <3>3, <3>4 DEF TypeOK
  <2>2. pc = "Done" => U = {} BY <2>1, Init
  <2>3. UV \in DomainPartitions
    <3>1. UV = {1..Len(seq0)} BY <2>1
    <3>2. UV \in SUBSET SUBSET (1..Len(seq0)) BY <3>1, Inv
    <3>3. (UNION UV) = 1..Len(seq0) BY <3>1
    <3>4. 1..Len(seq0) = Min(1..Len(seq0))..Max(1..Len(seq0)) BY <3>1
    <3>5. \A I, J \in UV : I = J BY <3>1
    <3>6. QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF DomainPartitions
  <2>4. seq \in PermsOf(seq0)
    <3>1. seq \in PermsOf(seq) BY <2>1
    <3>2. QED BY <3>1
  <2>5. UNION UV = 1..Len(seq0) BY <2>1, Inv, TypeOK, DomainPartitions, RelSorted, UV
  <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J) BY <2>1, Inv, TypeOK, DomainPartitions, RelSorted, UV
  <2>7. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
  <2>1. CASE a
    <3> SUFFICES ASSUME a
         PROVE Inv'
      OBVIOUS
    <3>1. CASE U # {}
      <4>1. /\ pc = "a" /\ pc' = "a" BY <3>1
      <4>2. PICK I \in U : a!2!2!1!(I) BY <3>1
      <4>3. CASE Cardinality(I) = 1
        <5>1. /\ U' = U \ {I} /\ seq' = seq /\ seq0' = seq0 /\ pc' = "a" BY <4>2, <4>3
        <5>2. QED
          <6>1. UV' = UV BY <4>1, <4>3, <5>1
          <6>2. TypeOK' BY <4>1, <4>3, <5>1, Inv, DomainPartitions, Min, Max, UV
          <6>3. ((pc = "Done") => (U = {}))' BY <4>1, <4>3, <5>1, Inv, DomainPartitions, Min, Max, UV
          <6>4. (UV \in DomainPartitions)' BY <4>1, <4>3, <5>1, <6>1, Inv, DomainPartitions
          <6>5. (seq \in PermsOf(seq0))' BY <4>1, <4>3, <5>1, Inv, DomainPartitions, PermsOf
          <6>6. (UNION UV = 1..Len(seq0))' BY <5>1, <6>1, Inv
          <6>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))' BY <4>1, <4>3, <5>1, <6>1, Inv, RelSorted
          <6>8. QED BY <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, Inv
        <5>3. CASE Cardinality(I) # 1
          <6>1. seq0' = seq0 BY <5>1
          <6>2. PICK p \in Min(I) .. (Max(I)-1) :
                     /\ seq' \in Partitions(I, p, seq)
                     /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
            BY <5>1, <5>3
          <6>3. /\ /\ Min(I)..p # {} /\ Min(I)..p = Min(Min(I)..p)..Max(Min(I)..p) /\ Min(I)..p \subseteq 1..Len(seq0)
                 /\ (p+1)..Max(I) # {} /\ (p+1)..Max(I) = Min((p+1)..Max(I))..Max((p+1)..Max(I)) /\ (p+1)..Max(I) \subseteq 1..Len(seq0)
                 /\ Min(I)..p \cap (p+1)..Max(I) = {}
                 /\ Min(I)..p \cup (p+1)..Max(I) = I
                 /\ \A i \in Min(I)..p, j \in (p+1)..Max(I) : (i < j) /\ (seq[i] =< seq[j])
            BY <5>2
          <6>4. /\ Len(seq) = Len(seq') /\ Len(seq) = Len(seq0) BY <5>2
          <6>5. UNION U = UNION U' BY <5>2, <5>3
          <6>6. UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)} BY <5>1, <5>2, <5>3, <5>4, <5>5, UV
          <6>7. TypeOK' BY <5>2, <5>3, <5>4, <6>2, <6>3, <6>5, <6>6, <6>1, Inv, DomainPartitions, Min, Max, UV
          <6>8. ((pc = "Done") => (U = {}))' BY <5>1, Inv, DomainPartitions, Min, Max, UV
          <6>9. (UV \in DomainPartitions)' BY <5>2, <5>3, <6>2, <6>3, <6>5, <6>6, <6>1, Inv, DomainPartitions, Min, Max, UV
          <6>10. (seq \in PermsOf(seq0))' BY <5>2, <5>4, <5>5, Inv, PermsOf
          <6>11. (UNION UV = 1..Len(seq0))' BY <5>5, <5>6, <6>1, Inv
          <6>12. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))' BY <5>2, <5>3, <5>4, <5>5, <6>2, <6>3, <6>5, <6>6, <6>1, Inv, RelSorted
          <6>13. QED BY <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, <6>10, <6>11, <6>12, Inv
        <5>4. QED BY <5>1, <5>3, <5>5, <5>6, <5>13
      <4>4. CASE U = {}
        <5>1. /\ pc = "a" /\ pc' = "Done" /\ seq' = seq /\ seq0' = seq0 BY <4>1
        <5>2. QED BY <5>1, Inv, DomainPartitions, Min, Max, UV
        <5>3. TypeOK' BY <5>1, Inv, DomainPartitions, Min, Max, UV
        <5>4. ((pc = "Done") => (U = {}))' BY <5>1, Inv, DomainPartitions, Min, Max, UV
        <5>5. (UV \in DomainPartitions)' BY <5>1, Inv, DomainPartitions
        <5>6. (seq \in PermsOf(seq0))' BY <5>1, Inv, PermsOf
        <5>7. (UNION UV = 1..Len(seq0))' BY <5>1, Inv
        <5>8. (\A I, J \in UV : (I # J) => RelSorted(I, J))' BY <5>1, Inv, RelSorted
        <5>9. QED BY <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, Inv
      <4>5. QED BY <4>3, <4>4
    <3>2. CASE UNCHANGED vars
      <4>1. TypeOK' BY <3>2, Inv, TypeOK
      <4>2. ((pc = "Done") => (U = {}))' BY <3>2, Inv, DomainPartitions
      <4>3. (UV \in DomainPartitions)' BY <3>2, Inv, DomainPartitions
      <4>4. (seq \in PermsOf(seq0))' BY <3>2, Inv, PermsOf
      <4>5. (UNION UV = 1..Len(seq0))' BY <3>2, Inv
      <4>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))' BY <3>2, Inv, RelSorted
      <4>7. QED BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, Inv
    <3>3. QED BY <3>1, <3>2
  <2>2. CASE UNCHANGED vars
    <3>1. TypeOK' BY <2>2, Inv, TypeOK
    <3>2. ((pc = "Done") => (U = {}))' BY <2>2, Inv
    <3>3. (UV \in DomainPartitions)' BY <2>2, Inv
    <3>4. (seq \in PermsOf(seq0))' BY <2>2, Inv
    <3>5. (UNION UV = 1..Len(seq0))' BY <2>2, Inv
    <3>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))' BY <2>2, Inv
    <3>7. QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, Inv
  <2>3. QED BY <2>1, <2>2, Inv, PTL
<1>3. Inv => PCorrect
  <2> SUFFICES ASSUME Inv, pc = "Done" PROVE seq \in PermsOf(seq0) /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q] BY PCorrect
  <2>1. seq \in PermsOf(seq0) BY <2>1, Inv
  <2>2. \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    <3> SUFFICES ASSUME p \in 1..Len(seq), q \in 1..Len(seq), p < q PROVE seq[p] =< seq[q] OBVIOUS
    <3>1. /\ Len(seq) = Len(seq0) /\ Len(seq) \in Nat /\ Len(seq) > 0 BY Inv
    <3>2. UV = {{i} : i \in 1..Len(seq)} BY U = {} DEF Inv, UV, TypeOK
    <3>3. {p} \in UV /\ {q} \in UV BY <3>1, <3>2
    <3> QED BY <3>3, Inv, RelSorted
  <2>3. QED BY <2>1, <2>2
<1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec
====