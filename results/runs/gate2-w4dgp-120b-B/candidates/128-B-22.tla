---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems
CONSTANT Values
ASSUME Values \subseteq Nat /\ Values # {}
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
  /\ seq0' = seq0

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
  <2>1. TypeOK
    OBVIOUS
  <2>2. (pc = "Done") => (U = {})
    OBVIOUS
  <2>3. UV \in DomainPartitions
    OBVIOUS
  <2>4. seq \in PermsOf(seq0)
    OBVIOUS
  <2>5. UNION UV = 1..Len(seq0)
    OBVIOUS
  <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J)
    OBVIOUS
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. CASE a
    <3>1. CASE U # {}
      <4>1. /\ pc = "a"
            /\ pc' = "a"
        OBVIOUS
      <4>2. PICK I \in U : a!2!2!1!(I)
        OBVIOUS
      <4>3. CASE Cardinality(I) = 1
        <5>1. /\ U' = U \ {I}
              /\ seq' = seq
          OBVIOUS
        <5>2. QED
          <6>1. UV' = UV
            OBVIOUS
          <6>2. TypeOK'
            BY <4>1, <4>3, <5>1 
            OBVIOUS
          <6>3. ((pc = "Done") => (U = {}))'
            BY <4>1, <4>3, <5>1 
            OBVIOUS
          <6>4. (UV \in DomainPartitions)'
            BY <4>1, <4>3, <5>1 
            OBVIOUS
          <6>5. (seq \in PermsOf(seq0))'
            BY <4>1, <4>3, <5>1 
            OBVIOUS
          <6>6. (UNION UV = 1..Len(seq0))'
            BY <5>1, <6>1 
            OBVIOUS
          <6>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
            BY <4>1, <4>3, <5>1, <6>1 
            OBVIOUS
          <6>8. QED
            BY <6>2, <6>3, <6>4, <6>5, <6>6, <6>7 DEF Inv
      <4>4. CASE Cardinality(I) # 1
        <5>1. seq0' = seq0
          BY DEF a
        <5>2. PICK p \in Min(I) .. (Max(I)-1) : 
                 /\ seq' \in Partitions(I, p, seq)
                 /\ U' = ((U \ {I}) \cup {Min(I)..p, (p+1)..Max(I)})
          OBVIOUS
        <5>3. /\ /\ Min(I)..p # {}
                 /\ Min(I)..p = Min(Min(I)..p)..Max(Min(I)..p)
                 /\ Min(I)..p \subseteq 1..Len(seq0)
              /\ /\ (p+1)..Max(I) # {}
                 /\ (p+1)..Max(I) = Min((p+1)..Max(I))..Max((p+1)..Max(I))
                 /\ (p+1)..Max(I) \subseteq 1..Len(seq0)
              /\ (Min(I)..p) \cap ((p+1)..Max(I)) = {}
              /\ (Min(I)..p) \cup ((p+1)..Max(I)) = I
              /\ \A i \in Min(I)..p, j \in (p+1)..Max(I) : (i < j) /\ (seq[i] =< seq[j])
          OBVIOUS
        <5>4. /\ Len(seq) = Len(seq')
              /\ Len(seq) = Len(seq0)
          OBVIOUS
        <5>5. UNION U = UNION U'
          OBVIOUS
        <5>6. UV' = (UV \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
          OBVIOUS
        <5>7. TypeOK'
          OBVIOUS
        <5>8. ((pc = "Done") => (U = {}))'
          BY <4>1
        <5>9. (UV \in DomainPartitions)'
          OBVIOUS
        <5>10. (seq \in PermsOf(seq0))'
          OBVIOUS
        <5>11. (UNION UV = 1..Len(seq0))'
          OBVIOUS
        <5>12. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
          OBVIOUS
        <5>13. QED
          BY <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, <5>10, <5>11, <5>12 DEF Inv
      <4>5. QED
        BY <4>3, <4>4
    <3>2. CASE U = {}
      <4>1. TypeOK' /\ ((pc = "Done") => (U = {}))
             /\ (UV \in DomainPartitions) /\ (seq \in PermsOf(seq0))
             /\ (UNION UV = 1..Len(seq0))
             /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))
        OBVIOUS
  <2>2. CASE UNCHANGED vars
    <3>1. TypeOK' /\ ((pc = "Done") => (U = {}))
           /\ (UV \in DomainPartitions) /\ (seq \in PermsOf(seq0))
           /\ (UNION UV = 1..Len(seq0))
           /\ (\A I, J \in UV : (I # J) => RelSorted(I, J))
      OBVIOUS
  <2>3. QED
    BY <2>1, <2>2 DEF Next
<1>3. Inv => PCorrect
  <2> SUFFICES ASSUME Inv, pc = "Done"
               PROVE  /\ seq \in PermsOf(seq0)
                      /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    BY DEF PCorrect
  <2>1. seq \in PermsOf(seq0)
    BY DEF Inv
  <2>2. \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    <3> SUFFICES ASSUME p \in 1..Len(seq), q \in 1..Len(seq), p < q
                 PROVE seq[p] =< seq[q]
      OBVIOUS
    <3>1. /\ Len(seq) = Len(seq0)
          /\ Len(seq) \in Nat /\ Len(seq) > 0
          /\ UV = {{i} : i \in 1..Len(seq)}
          /\ {p} \in UV /\ {q} \in UV
      OBVIOUS
    <3>2. QED
      BY <3>1 DEF RelSorted
  <2>3. QED
    BY <2>1, <2>2
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Spec
====